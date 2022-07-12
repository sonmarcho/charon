//! Implementations for llbc_ast.rs

#![allow(dead_code)]
use std::ops::DerefMut;

use crate::expressions::{Operand, Place, Rvalue};
use crate::formatter::Formatter;
use crate::im_ast::{fmt_call, FunDeclId, FunSigFormatter, GAstFormatter, GlobalDeclId, TAB_INCR};
use crate::llbc_ast::{Call, FunDecl, FunDecls, GlobalDecl, GlobalDecls, Statement, SwitchTargets};
use crate::types::*;
use crate::values::*;
use crate::{common::*, id_vector};
use itertools::chain;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use take_mut::take;

/// Goes from e.g. [A, B, C] ; D to (A, (B, (C, D))).
pub fn chain_statements(firsts: Vec<Statement>, last: Statement) -> Statement {
    firsts.into_iter().rev().fold(last, |cont, bind| {
        assert!(!bind.is_sequence());
        Statement::Sequence(Box::new(bind), Box::new(cont))
    })
}

/// Utility function for [new_sequence].
/// Efficiently appends a new statement at the rightmost place of a well-formed sequence.
fn append_rightmost(seq: &mut Statement, r: Box<Statement>) {
    let (_l1, l2) = match seq {
        Statement::Sequence(l1, l2) => (l1, l2),
        _ => unreachable!(),
    };
    if l2.is_sequence() {
        append_rightmost(l2, r);
    } else {
        take(l2.deref_mut(), move |l2| {
            Statement::Sequence(Box::new(l2), r)
        });
    }
}

/// Builds a sequence from well-formed statements.
/// Ensures that the left statement will not be a sequence in the new sequence:
/// Must be used instead of the raw [Statement::Sequence] constructor,
/// unless you're sure that the left statement is not a sequence.
pub fn new_sequence(mut l: Statement, r: Statement) -> Statement {
    let r = Box::new(r);
    match l {
        Statement::Sequence(_, _) => {
            append_rightmost(&mut l, r);
            l
        }
        l => Statement::Sequence(Box::new(l), r),
    }
}

/// Visit an rvalue and generate statements. Used below in [transform_operands].
fn transform_rvalue_operands<F: FnMut(&mut Operand) -> Vec<Statement>>(
    rval: &mut Rvalue,
    f: &mut F,
) -> Vec<Statement> {
    match rval {
        Rvalue::Use(op) | Rvalue::UnaryOp(_, op) => f(op),
        Rvalue::BinaryOp(_, o1, o2) => chain(f(o1), f(o2)).collect(),
        Rvalue::Aggregate(_, ops) => ops.iter_mut().flat_map(f).collect(),
        Rvalue::Discriminant(_) | Rvalue::Ref(_, _) => vec![],
    }
}

/// Transform a statement by visiting its operands and inserting the generated
/// statements before each visited operand.
/// Useful to implement a pass on operands: see e.g. [extract_global_assignments.rs].
pub fn transform_operands<F: FnMut(&mut Operand) -> Vec<Statement>>(
    st: Statement,
    f: &mut F,
) -> Statement {
    // Does two matchs, depending if we want to move or to borrow the statement.
    let mut st = match st {
        // Recursive calls
        Statement::Loop(s) => Statement::Loop(Box::new(transform_operands(*s, f))),
        Statement::Sequence(s1, s2) => {
            new_sequence(transform_operands(*s1, f), transform_operands(*s2, f))
        }
        Statement::Switch(op, tgt) => Statement::Switch(
            op,
            match tgt {
                SwitchTargets::If(s1, s2) => SwitchTargets::If(
                    Box::new(transform_operands(*s1, f)),
                    Box::new(transform_operands(*s2, f)),
                ),
                SwitchTargets::SwitchInt(ty, vec, s) => SwitchTargets::SwitchInt(
                    ty,
                    vec.into_iter()
                        .map(|(v, s)| (v, transform_operands(s, f)))
                        .collect(),
                    Box::new(transform_operands(*s, f)),
                ),
            },
        ),
        _ => st,
    };
    let new_st = match &mut st {
        // Actual transformations
        Statement::Switch(op, _) => f(op),
        Statement::Assign(_, r) => transform_rvalue_operands(r, f),
        Statement::Call(c) => c.args.iter_mut().flat_map(f).collect(),
        Statement::Assert(a) => f(&mut a.cond),

        // Identity (complete match for compile-time errors when new statements are created)
        Statement::AssignGlobal(_, _)
        | Statement::FakeRead(_)
        | Statement::SetDiscriminant(_, _)
        | Statement::Drop(_)
        | Statement::Panic
        | Statement::Return
        | Statement::Break(_)
        | Statement::Continue(_)
        | Statement::Nop
        | Statement::Sequence(_, _)
        | Statement::Loop(_) => vec![],
    };
    chain_statements(new_st, st)
}

impl SwitchTargets {
    pub fn get_targets(&self) -> Vec<&Statement> {
        match self {
            SwitchTargets::If(exp1, exp2) => {
                vec![exp1, exp2]
            }
            SwitchTargets::SwitchInt(_, targets, otherwise) => {
                let mut out: Vec<&Statement> = vec![otherwise];
                for (_, tgt) in targets {
                    out.push(tgt);
                }
                out
            }
        }
    }
}

impl Serialize for SwitchTargets {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "SwitchTargets";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            SwitchTargets::If(e1, e2) => {
                vs.serialize_field(e1)?;
                vs.serialize_field(e2)?;
            }
            SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                vs.serialize_field(int_ty)?;
                let targets: Vec<(VecSerializer<ScalarValue>, &Statement)> = targets
                    .iter()
                    .map(|(values, st)| (VecSerializer::new(values), st))
                    .collect();
                let targets = VecSerializer::new(&targets);
                vs.serialize_field(&targets)?;
                vs.serialize_field(otherwise)?;
            }
        }
        vs.end()
    }
}

impl Statement {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Statement::Assign(place, rvalue) => format!(
                "{}{} := {}",
                tab,
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            )
            .to_owned(),
            Statement::AssignGlobal(id, gid) => format!(
                "{}{} := {}",
                tab,
                ctx.format_object(*id),
                ctx.format_object(*gid),
            )
            .to_owned(),
            Statement::FakeRead(place) => {
                format!("{}@fake_read({})", tab, place.fmt_with_ctx(ctx)).to_owned()
            }
            Statement::SetDiscriminant(place, variant_id) => format!(
                "{}@discriminant({}) := {}",
                tab,
                place.fmt_with_ctx(ctx),
                variant_id.to_string()
            )
            .to_owned(),
            Statement::Drop(place) => format!("{}drop {}", tab, place.fmt_with_ctx(ctx)).to_owned(),
            Statement::Assert(assert) => format!(
                "{}assert({} == {})",
                tab,
                assert.cond.fmt_with_ctx(ctx),
                assert.expected,
            )
            .to_owned(),
            Statement::Call(call) => {
                let Call {
                    func,
                    region_args,
                    type_args,
                    args,
                    dest,
                } = call;
                let call = fmt_call(ctx, func, region_args, type_args, args);
                format!("{}{} := {}", tab, dest.fmt_with_ctx(ctx), call).to_owned()
            }
            Statement::Panic => format!("{}panic", tab).to_owned(),
            Statement::Return => format!("{}return", tab).to_owned(),
            Statement::Break(index) => format!("{}break {}", tab, index).to_owned(),
            Statement::Continue(index) => format!("{}continue {}", tab, index).to_owned(),
            Statement::Nop => format!("{}nop", tab).to_owned(),
            Statement::Sequence(st1, st2) => format!(
                "{}\n{}",
                st1.fmt_with_ctx(tab, ctx),
                st2.fmt_with_ctx(tab, ctx)
            )
            .to_owned(),
            Statement::Switch(discr, targets) => match targets {
                SwitchTargets::If(true_st, false_st) => {
                    let inner_tab = format!("{}{}", tab, TAB_INCR);
                    format!(
                        "{}if {} {{\n{}\n{}}}\n{}else {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        true_st.fmt_with_ctx(&inner_tab, ctx),
                        tab,
                        tab,
                        false_st.fmt_with_ctx(&inner_tab, ctx),
                        tab,
                    )
                    .to_owned()
                }
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let inner_tab1 = format!("{}{}", tab, TAB_INCR);
                    let inner_tab2 = format!("{}{}", inner_tab1, TAB_INCR);
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(pvl, st)| {
                            // Note that there may be several pattern values
                            let pvl: Vec<String> = pvl.iter().map(|v| v.to_string()).collect();
                            format!(
                                "{}{} => {{\n{}\n{}}}",
                                inner_tab1,
                                pvl.join(" | "),
                                st.fmt_with_ctx(&inner_tab2, ctx),
                                inner_tab1
                            )
                            .to_owned()
                        })
                        .collect();
                    maps.push(
                        format!(
                            "{}_ => {{\n{}\n{}}}",
                            inner_tab1,
                            otherwise.fmt_with_ctx(&inner_tab2, ctx),
                            inner_tab1
                        )
                        .to_owned(),
                    );
                    let maps = maps.join(",\n");

                    format!(
                        "{}switch {} {{\n{}\n{}}}",
                        tab,
                        discr.fmt_with_ctx(ctx),
                        maps,
                        tab
                    )
                    .to_owned()
                }
            },
            Statement::Loop(body) => {
                let inner_tab = format!("{}{}", tab, TAB_INCR);
                format!(
                    "{}loop {{\n{}\n{}}}",
                    tab,
                    body.fmt_with_ctx(&inner_tab, ctx),
                    tab
                )
                .to_owned()
            }
        }
    }
}

type AstFormatter<'ctx> = GAstFormatter<'ctx, FunDecls, GlobalDecls>;

impl<'ctx> Formatter<FunDeclId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: FunDeclId::Id) -> String {
        let f = self.fun_context.get(id).unwrap();
        f.name.to_string()
    }
}

impl<'ctx> Formatter<GlobalDeclId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        let c = self.global_context.get(id).unwrap();
        c.name.to_string()
    }
}

impl<'ctx> Formatter<&Statement> for AstFormatter<'ctx> {
    fn format_object(&self, st: &Statement) -> String {
        st.fmt_with_ctx(TAB_INCR, self)
    }
}

impl<'ctx> Formatter<&Rvalue> for AstFormatter<'ctx> {
    fn format_object(&self, v: &Rvalue) -> String {
        v.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<&Place> for AstFormatter<'ctx> {
    fn format_object(&self, p: &Place) -> String {
        p.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<&Operand> for AstFormatter<'ctx> {
    fn format_object(&self, op: &Operand) -> String {
        op.fmt_with_ctx(self)
    }
}

impl FunDecl {
    pub fn fmt_with_defs<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDecls,
        const_ctx: &'ctx GlobalDecls,
    ) -> String {
        // Initialize the contexts
        let fun_sig_ctx = FunSigFormatter {
            ty_ctx,
            sig: &self.signature,
        };

        // We cheat a bit: if there is a body, we take its locals, otherwise
        // we use []:
        let empty = VarId::Vector::new();
        let locals = match &self.body {
            None => &empty,
            Some(body) => &body.locals,
        };

        let eval_ctx = AstFormatter::new(
            ty_ctx,
            fun_ctx,
            const_ctx,
            &self.signature.type_params,
            locals,
        );

        // Use the contexts for printing
        self.gfmt_with_ctx("", &fun_sig_ctx, &eval_ctx)
    }
}

impl GlobalDecl {
    pub fn fmt_with_defs<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDecls,
        const_ctx: &'ctx GlobalDecls,
    ) -> String {
        // We cheat a bit: if there is a body, we take its locals, otherwise
        // we use []:
        let empty = VarId::Vector::new();
        let locals = match &self.body {
            None => &empty,
            Some(body) => &body.locals,
        };

        let empty = id_vector::Vector::new();
        let eval_ctx = AstFormatter::new(ty_ctx, fun_ctx, const_ctx, &empty, locals);

        // Use the contexts for printing
        self.gfmt_with_ctx("", &eval_ctx)
    }
}
