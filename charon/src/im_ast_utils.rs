//! Implementations for im_ast.rs
#![allow(dead_code)]

use crate::common::*;
use crate::expressions::*;
use crate::formatter::Formatter;
use crate::id_vector;
use crate::im_ast::*;
use crate::names::Name;
use crate::types::*;
use crate::values::*;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::cmp::max;
use std::fmt::Debug;
use std::iter::FromIterator;

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
pub fn iter_function_bodies<T: Debug + Clone + Serialize>(
    funs: &mut FunDeclId::Vector<GFunDecl<T>>,
) -> impl Iterator<Item = (&Name, &mut GExprBody<T>)> {
    funs.iter_mut().flat_map(|f| match f.body.as_mut() {
        None => None, // Option::map was complaining about borrowing f
        Some(b) => Some((&f.name, b)),
    })
}

/// Iterate on the declarations' non-empty bodies with their corresponding name and type.
/// Same as [iter_function_bodies] (but the `flat_map` lambda cannot be generic).
pub fn iter_global_bodies<T: Debug + Clone + Serialize>(
    globals: &mut GlobalDeclId::Vector<GGlobalDecl<T>>,
) -> impl Iterator<Item = (&Name, &mut GExprBody<T>)> {
    globals.iter_mut().flat_map(|g| match g.body.as_mut() {
        None => None, // Option::map was complaining about borrowing g
        Some(b) => Some((&g.name, b)),
    })
}

/// Makes a lambda that generates a new variable id, pushes a new variable in
/// the body locals with the given type and returns its id.
pub fn make_locals_generator<'a>(
    locals: &'a mut VarId::Vector<Var>,
) -> impl FnMut(ETy) -> VarId::Id + 'a {
    let mut next_id = locals.iter().fold(VarId::ZERO, |id, v| max(id, v.index));
    move |ty| {
        next_id.incr();
        let id = next_id;
        locals.push_back(Var {
            index: id,
            name: None,
            ty,
        });
        id
    }
}

impl std::string::ToString for Var {
    fn to_string(&self) -> String {
        let id = var_id_to_pretty_string(self.index);
        match &self.name {
            // We display both the variable name and its id because some
            // variables may have the same name (in different scopes)
            Some(name) => format!("{}({})", name, id),
            None => id,
        }
    }
}

impl Var {
    /// Substitute the region parameters and type variables and return
    /// the resulting variable
    pub fn substitute(&self, subst: &ETypeSubst) -> Var {
        Var {
            index: self.index,
            name: self.name.clone(),
            ty: self.ty.substitute_types(subst),
        }
    }
}

impl SwitchTargets {
    pub fn get_targets(&self) -> Vec<BlockId::Id> {
        match self {
            SwitchTargets::If(then_tgt, else_tgt) => {
                vec![*then_tgt, *else_tgt]
            }
            SwitchTargets::SwitchInt(_, targets, otherwise) => {
                let mut all_targets = vec![];
                for (_, target) in targets {
                    all_targets.push(*target);
                }
                all_targets.push(*otherwise);
                all_targets
            }
        }
    }

    /// Perform a type substitution - actually simply clone the object
    pub fn substitute(&self, _subst: &ETypeSubst) -> Self {
        self.clone()
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
            SwitchTargets::If(id1, id2) => {
                vs.serialize_field(id1)?;
                vs.serialize_field(id2)?;
            }
            SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                vs.serialize_field(int_ty)?;
                let targets = LinkedHashMapSerializer::new(targets);
                vs.serialize_field(&targets)?;
                vs.serialize_field(otherwise)?;
            }
        }
        vs.end()
    }
}

impl Statement {
    /// Substitute the type variables and return the resulting statement.
    pub fn substitute(&self, subst: &ETypeSubst) -> Statement {
        match self {
            Statement::Assign(place, rvalue) => {
                Statement::Assign(place.substitute(subst), rvalue.substitute(subst))
            }
            Statement::FakeRead(place) => Statement::FakeRead(place.substitute(subst)),
            Statement::SetDiscriminant(place, variant_id) => {
                Statement::SetDiscriminant(place.substitute(subst), *variant_id)
            }
            Statement::StorageDead(var_id) => Statement::StorageDead(*var_id),
        }
    }
}

impl Terminator {
    /// Substitute the type variables and return the resulting terminator
    pub fn substitute(&self, subst: &ETypeSubst) -> Terminator {
        match self {
            Terminator::Goto { target } => Terminator::Goto { target: *target },
            Terminator::Switch { discr, targets } => Terminator::Switch {
                discr: discr.substitute(subst),
                targets: targets.substitute(subst),
            },
            Terminator::Panic => Terminator::Panic,
            Terminator::Return => Terminator::Return,
            Terminator::Unreachable => Terminator::Unreachable,
            Terminator::Drop { place, target } => Terminator::Drop {
                place: place.substitute(subst),
                target: *target,
            },
            Terminator::Call {
                func,
                region_args,
                type_args,
                args,
                dest,
                target,
            } => Terminator::Call {
                func: func.clone(),
                region_args: region_args.clone(),
                type_args: type_args
                    .iter()
                    .map(|ty| ty.substitute_types(subst))
                    .collect(),
                args: Vec::from_iter(args.iter().map(|arg| arg.substitute(subst))),
                dest: dest.substitute(subst),
                target: *target,
            },
            Terminator::Assert {
                cond,
                expected,
                target,
            } => Terminator::Assert {
                cond: cond.substitute(subst),
                expected: *expected,
                target: *target,
            },
        }
    }
}

impl BlockData {
    /// Substitute the type variables and return the resulting `BlockData`
    pub fn substitute(&self, subst: &ETypeSubst) -> BlockData {
        let statements = self
            .statements
            .iter()
            .map(|x| x.substitute(subst))
            .collect();
        let terminator = self.terminator.substitute(subst);
        BlockData {
            statements,
            terminator,
        }
    }
}

impl Statement {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Statement::Assign(place, rvalue) => format!(
                "{} := {}",
                place.fmt_with_ctx(ctx),
                rvalue.fmt_with_ctx(ctx),
            )
            .to_owned(),
            Statement::FakeRead(place) => {
                format!("@fake_read({})", place.fmt_with_ctx(ctx),).to_owned()
            }
            Statement::SetDiscriminant(place, variant_id) => format!(
                "@discriminant({}) := {}",
                place.fmt_with_ctx(ctx),
                variant_id.to_string()
            )
            .to_owned(),
            Statement::StorageDead(vid) => {
                format!("@storage_dead({})", var_id_to_pretty_string(*vid)).to_owned()
            }
        }
    }
}

impl<'ctx> Formatter<&Statement> for AstFormatter<'ctx> {
    fn format_object(&self, statement: &Statement) -> String {
        statement.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<&BlockId::Vector<BlockData>> for AstFormatter<'ctx> {
    fn format_object(&self, body: &BlockId::Vector<BlockData>) -> String {
        fmt_body_blocks_with_ctx(body, TAB_INCR, self)
    }
}

pub fn fmt_call<'a, 'b, T>(
    ctx: &'b T,
    func: &'a FunId,
    region_args: &'a Vec<ErasedRegion>,
    type_args: &'a Vec<ETy>,
    args: &'a Vec<Operand>,
) -> String
where
    T: Formatter<VarId::Id>
        + Formatter<TypeVarId::Id>
        + Formatter<&'a ErasedRegion>
        + Formatter<TypeDeclId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<(TypeDeclId::Id, VariantId::Id)>
        + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
{
    let rt_args = if region_args.len() + type_args.len() == 0 {
        "".to_owned()
    } else {
        let regions_s: Vec<String> = region_args.iter().map(|x| x.to_string()).collect();
        let mut types_s: Vec<String> = type_args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
        let mut s = regions_s;
        s.append(&mut types_s);
        format!("<{}>", s.join(", ")).to_owned()
    };
    let args: Vec<String> = args.iter().map(|x| x.fmt_with_ctx(ctx)).collect();
    let args = args.join(", ");

    let f = match func {
        FunId::Regular(def_id) => format!("{}{}", ctx.format_object(*def_id), rt_args).to_string(),
        FunId::Assumed(assumed) => match assumed {
            AssumedFunId::Replace => format!("core::mem::replace{}", rt_args).to_string(),
            AssumedFunId::BoxNew => format!("alloc::boxed::Box{}::new", rt_args).to_string(),
            AssumedFunId::BoxDeref => format!(
                "core::ops::deref::Deref<alloc::boxed::Box{}>::deref",
                rt_args
            )
            .to_string(),
            AssumedFunId::BoxDerefMut => format!(
                "core::ops::deref::DerefMut<alloc::boxed::Box{}>::deref_mut",
                rt_args
            )
            .to_string(),
            AssumedFunId::BoxFree => format!("alloc::alloc::box_free{}", rt_args).to_string(),
            AssumedFunId::VecNew => format!("alloc::vec::Vec{}::new", rt_args).to_string(),
            AssumedFunId::VecPush => format!("alloc::vec::Vec{}::push", rt_args).to_string(),
            AssumedFunId::VecInsert => format!("alloc::vec::Vec{}::insert", rt_args).to_string(),
            AssumedFunId::VecLen => format!("alloc::vec::Vec{}::len", rt_args).to_string(),
            AssumedFunId::VecIndex => {
                format!("core::ops::index::Index<alloc::vec::Vec{}>::index", rt_args).to_string()
            }
            AssumedFunId::VecIndexMut => format!(
                "core::ops::index::IndexMut<alloc::vec::Vec{}>::index_mut",
                rt_args
            )
            .to_string(),
        },
    };

    format!("{}({})", f, args,).to_string()
}

impl Terminator {
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDeclId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        match self {
            Terminator::Goto { target } => format!("goto bb{}", target.to_string()).to_string(),
            Terminator::Switch { discr, targets } => match targets {
                SwitchTargets::If(true_block, false_block) => format!(
                    "if {} -> bb{} else -> bb{}",
                    discr.fmt_with_ctx(ctx),
                    true_block.to_string(),
                    false_block.to_string()
                )
                .to_string(),
                SwitchTargets::SwitchInt(_ty, maps, otherwise) => {
                    let mut maps: Vec<String> = maps
                        .iter()
                        .map(|(v, bid)| {
                            format!("{}: bb{}", v.to_string(), bid.to_string()).to_string()
                        })
                        .collect();
                    maps.push(format!("otherwise: bb{}", otherwise.to_string()).to_string());
                    let maps = maps.join(", ");

                    format!("switch {} -> {}", discr.fmt_with_ctx(ctx), maps).to_string()
                }
            },
            Terminator::Panic => "panic".to_string(),
            Terminator::Return => "return".to_string(),
            Terminator::Unreachable => "unreachable".to_string(),
            Terminator::Drop { place, target } => format!(
                "drop {} -> bb{}",
                place.fmt_with_ctx(ctx),
                target.to_string()
            )
            .to_string(),
            Terminator::Call {
                func,
                region_args,
                type_args,
                args,
                dest,
                target,
            } => {
                let call = fmt_call(ctx, func, region_args, type_args, args);

                format!(
                    "{} := {} -> bb{}",
                    dest.fmt_with_ctx(ctx),
                    call,
                    target.to_string(),
                )
                .to_string()
            }
            Terminator::Assert {
                cond,
                expected,
                target,
            } => format!(
                "assert({} == {}) -> bb{}",
                cond.fmt_with_ctx(ctx),
                expected,
                target.to_string()
            )
            .to_string(),
        }
    }
}

impl BlockData {
    pub fn fmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDeclId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
    {
        let mut out: Vec<String> = Vec::new();

        // Format the statements
        for statement in &self.statements {
            out.push(format!("{}{};\n", tab, statement.fmt_with_ctx(ctx)).to_owned());
        }

        // Format the terminator
        out.push(format!("{}{};", tab, self.terminator.fmt_with_ctx(ctx)).to_owned());

        // Join the strings
        out.join("")
    }
}

fn fmt_body_blocks_with_ctx<'a, 'b, 'c, C>(
    body: &'a BlockId::Vector<BlockData>,
    tab: &'b str,
    ctx: &'c C,
) -> String
where
    C: Formatter<VarId::Id>
        + Formatter<TypeVarId::Id>
        + Formatter<&'a ErasedRegion>
        + Formatter<TypeDeclId::Id>
        + Formatter<FunDeclId::Id>
        + Formatter<GlobalDeclId::Id>
        + Formatter<(TypeDeclId::Id, VariantId::Id)>
        + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>,
{
    let block_tab = format!("{}{}", tab, TAB_INCR);
    let mut blocks: Vec<String> = Vec::new();
    for (bid, block) in body.iter_indexed_values() {
        use crate::id_vector::ToUsize;
        blocks.push(
            format!(
                "{}bb{}: {{\n{}\n{}}}\n",
                tab,
                bid.to_usize(),
                block.fmt_with_ctx(&block_tab, ctx),
                tab
            )
            .to_owned(),
        );
    }
    blocks.join("\n")
}

impl<T: Debug + Clone + Serialize> GExprBody<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_defs`](FunDecl::fmt_with_defs).
    pub fn fmt_with_ctx<'a, 'b, 'c, C>(&'a self, tab: &'b str, ctx: &'c C) -> String
    where
        C: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<TypeDeclId::Id>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a T>,
    {
        // Format the local variables
        let mut locals: Vec<String> = Vec::new();
        for v in &self.locals {
            use crate::id_vector::ToUsize;
            let index = v.index.to_usize();
            let comment = if index == 0 {
                "// return".to_owned()
            } else {
                if index <= self.arg_count {
                    format!("// arg #{}", index).to_owned()
                } else {
                    match &v.name {
                        Some(_) => "// local".to_owned(),
                        None => "// anonymous local".to_owned(),
                    }
                }
            };

            let var_name = match &v.name {
                Some(name) => name.clone(),
                None => var_id_to_pretty_string(v.index),
            };

            locals.push(
                format!(
                    "{}let {}: {}; {}\n",
                    tab,
                    var_name,
                    v.ty.fmt_with_ctx(ctx),
                    comment
                )
                .to_owned(),
            );
        }

        let mut locals = locals.join("");
        locals.push_str("\n");

        // Format the body blocks - TODO: we don't take the indentation
        // into account, here
        let body = ctx.format_object(&self.body);

        // Put everything together
        let mut out = locals;
        out.push_str(&body);
        out
    }
}

impl FunSig {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
    {
        // Type parameters
        let params = if self.region_params.len() + self.type_params.len() == 0 {
            "".to_owned()
        } else {
            let regions: Vec<String> = self.region_params.iter().map(|x| x.to_string()).collect();
            let mut types: Vec<String> = self.type_params.iter().map(|x| x.to_string()).collect();
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", ")).to_owned()
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for ty in &self.inputs {
            args.push(format!("{}", ty.fmt_with_ctx(ctx)).to_owned());
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_owned()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(ctx)).to_owned()
        };

        // Regions hierarchy
        let regions_hierarchy: Vec<String> = self
            .regions_hierarchy
            .iter()
            .map(|rg| rg.fmt_with_ctx(ctx))
            .collect();
        let regions_hierarchy = regions_hierarchy.join("\n");

        // Put everything together
        format!(
            "fn{}({}){}\n\nRegions hierarchy:\n{}",
            params, args, ret_ty, regions_hierarchy
        )
        .to_owned()
    }
}

pub struct FunSigFormatter<'a> {
    pub ty_ctx: &'a TypeDecls,
    pub sig: &'a FunSig,
}

impl<'a> Formatter<TypeVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.sig.type_params.get(id).unwrap().to_string()
    }
}

impl<'a> Formatter<RegionVarId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        self.sig.region_params.get(id).unwrap().to_string()
    }
}

impl<'a> Formatter<&Region<RegionVarId::Id>> for FunSigFormatter<'a> {
    fn format_object(&self, r: &Region<RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'a> Formatter<TypeDeclId::Id> for FunSigFormatter<'a> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.ty_ctx.format_object(id)
    }
}

impl FunSig {
    pub fn fmt_with_defs<'ctx>(&self, ty_ctx: &'ctx TypeDecls) -> String {
        // Initialize the formatting context
        let ctx = FunSigFormatter { ty_ctx, sig: self };

        // Use the context for printing
        self.fmt_with_ctx(&ctx)
    }
}

impl<T: Debug + Clone + Serialize> GFunDecl<T> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the function definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the function
    /// definition). See [`fmt_with_defs`](FunDecl::fmt_with_defs).
    pub fn gfmt_with_ctx<'a, 'b, 'c, T1, T2>(
        &'a self,
        tab: &'b str,
        sig_ctx: &'c T1,
        body_ctx: &'c T2,
    ) -> String
    where
        T1: Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>,
        T2: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a T>,
    {
        // Function name
        let name = self.name.to_string();

        // Type parameters
        let params = if self.signature.region_params.len() + self.signature.type_params.len() == 0 {
            "".to_owned()
        } else {
            let regions: Vec<String> = self
                .signature
                .region_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut types: Vec<String> = self
                .signature
                .type_params
                .iter()
                .map(|x| x.to_string())
                .collect();
            let mut params = regions;
            params.append(&mut types);
            format!("<{}>", params.join(", ")).to_owned()
        };

        // Arguments
        let mut args: Vec<String> = Vec::new();
        for i in 0..self.signature.inputs.len() {
            // The input variables start at index 1
            let id = VarId::Id::new(i + 1);
            let arg_ty = &self.signature.inputs.get(i).unwrap();
            args.push(
                format!(
                    "{}: {}",
                    var_id_to_pretty_string(id),
                    arg_ty.fmt_with_ctx(sig_ctx)
                )
                .to_owned(),
            );
        }
        let args = args.join(", ");

        // Return type
        let ret_ty = &self.signature.output;
        let ret_ty = if ret_ty.is_unit() {
            "".to_owned()
        } else {
            format!(" -> {}", ret_ty.fmt_with_ctx(sig_ctx)).to_owned()
        };

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{}fn {}{}({}){}", tab, name, params, args, ret_ty).to_owned()
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{}{}", tab, TAB_INCR);
                let body = body.fmt_with_ctx(&body_tab, body_ctx);

                // Put everything together
                format!(
                    "{}fn {}{}({}){} {{\n{}\n{}}}",
                    tab, name, params, args, ret_ty, body, tab
                )
                .to_owned()
            }
        }
    }
}

impl<CD: Debug + Clone + Serialize> GGlobalDecl<CD> {
    /// This is an auxiliary function for printing definitions. One may wonder
    /// why we require a formatter to format, for instance, (type) var ids,
    /// because the global definition already has the information to print
    /// variables. The reason is that it is easier for us to write this very
    /// generic auxiliary function, then apply it on an evaluation context
    /// properly initialized (with the information contained in the global
    /// definition). See [`fmt_with_defs`](FunDecl::fmt_with_defs).
    pub fn gfmt_with_ctx<'a, 'b, 'c, T>(&'a self, tab: &'b str, body_ctx: &'c T) -> String
    where
        T: Formatter<VarId::Id>
            + Formatter<TypeVarId::Id>
            + Formatter<TypeDeclId::Id>
            + Formatter<&'a ErasedRegion>
            + Formatter<FunDeclId::Id>
            + Formatter<GlobalDeclId::Id>
            + Formatter<(TypeDeclId::Id, VariantId::Id)>
            + Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
            + Formatter<&'a CD>,
    {
        // Decl name
        let name = self.name.to_string();

        // Case disjunction on the presence of a body (transparent/opaque definition)
        match &self.body {
            Option::None => {
                // Put everything together
                format!("{}global {}", tab, name).to_owned()
            }
            Option::Some(body) => {
                // Body
                let body_tab = format!("{}{}", tab, TAB_INCR);
                let body = body.fmt_with_ctx(&body_tab, body_ctx);

                // Put everything together
                format!("{}global {} {{\n{}\n{}}}", tab, name, body, tab).to_owned()
            }
        }
    }
}

pub struct GAstFormatter<'ctx, FD, CD> {
    pub type_context: &'ctx TypeDecls,
    pub fun_context: &'ctx FD,
    pub global_context: &'ctx CD,
    pub type_vars: &'ctx TypeVarId::Vector<TypeVar>,
    pub vars: &'ctx VarId::Vector<Var>,
}

type AstFormatter<'ctx> = GAstFormatter<'ctx, FunDecls, GlobalDecls>;

impl<'ctx> Formatter<FunDeclId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: FunDeclId::Id) -> String {
        let f = self.fun_context.get(id).unwrap();
        f.name.to_string()
    }
}

impl<'ctx> Formatter<&Terminator> for AstFormatter<'ctx> {
    fn format_object(&self, terminator: &Terminator) -> String {
        terminator.fmt_with_ctx(self)
    }
}

impl<'ctx> Formatter<GlobalDeclId::Id> for AstFormatter<'ctx> {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        let c = self.global_context.get(id).unwrap();
        c.name.to_string()
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

impl<'ctx, FD, CD> GAstFormatter<'ctx, FD, CD> {
    pub fn new(
        type_context: &'ctx TypeDecls,
        fun_context: &'ctx FD,
        global_context: &'ctx CD,
        type_vars: &'ctx TypeVarId::Vector<TypeVar>,
        vars: &'ctx VarId::Vector<Var>,
    ) -> Self {
        GAstFormatter {
            type_context,
            fun_context,
            global_context,
            type_vars,
            vars,
        }
    }
}

impl<'ctx, FD, CD> Formatter<VarId::Id> for GAstFormatter<'ctx, FD, CD> {
    fn format_object(&self, id: VarId::Id) -> String {
        let v = self.vars.get(id).unwrap();
        v.to_string()
    }
}

impl<'ctx, FD, CD> Formatter<TypeVarId::Id> for GAstFormatter<'ctx, FD, CD> {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        self.type_vars.get(id).unwrap().to_string()
    }
}

/// For adt types
impl<'ctx, FD, CD> Formatter<TypeDeclId::Id> for GAstFormatter<'ctx, FD, CD> {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        self.type_context.format_object(id)
    }
}

/// For enum values: `List::Cons`
impl<'ctx, FD, CD> Formatter<(TypeDeclId::Id, VariantId::Id)> for GAstFormatter<'ctx, FD, CD> {
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        let ctx = self.type_context;
        let def = ctx.get_type_def(def_id).unwrap();
        let variants = def.kind.as_enum();
        let mut name = def.name.to_string();
        let variant_name = &variants.get(variant_id).unwrap().name;
        name.push_str("::");
        name.push_str(variant_name);
        name
    }
}

/// For struct/enum values: retrieve a field name
impl<'ctx, FD, CD> Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)>
    for GAstFormatter<'ctx, FD, CD>
{
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (def_id, opt_variant_id, field_id) = id;
        let ctx = self.type_context;
        let gen_def = ctx.get_type_def(def_id).unwrap();
        match (&gen_def.kind, opt_variant_id) {
            (TypeDeclKind::Enum(variants), Some(variant_id)) => {
                let field = variants
                    .get(variant_id)
                    .unwrap()
                    .fields
                    .get(field_id)
                    .unwrap();
                match &field.name {
                    Option::Some(name) => name.clone(),
                    Option::None => field_id.to_string(),
                }
            }
            (TypeDeclKind::Struct(fields), None) => {
                let field = fields.get(field_id).unwrap();
                match &field.name {
                    Option::Some(name) => name.clone(),
                    Option::None => field_id.to_string(),
                }
            }
            _ => unreachable!(),
        }
    }
}

impl<'ctx, FD, CD> Formatter<&ErasedRegion> for GAstFormatter<'ctx, FD, CD> {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_owned()
    }
}

impl<'ctx, FD, CD> Formatter<&ETy> for GAstFormatter<'ctx, FD, CD> {
    fn format_object(&self, ty: &ETy) -> String {
        ty.fmt_with_ctx(self)
    }
}

impl FunDecl {
    pub fn fmt_with_defs<'ctx>(
        &self,
        ty_ctx: &'ctx TypeDecls,
        fun_ctx: &'ctx FunDecls,
        global_ctx: &'ctx GlobalDecls,
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
            global_ctx,
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
        global_ctx: &'ctx GlobalDecls,
    ) -> String {
        // We cheat a bit: if there is a body, we take its locals, otherwise
        // we use []:
        let empty = VarId::Vector::new();
        let locals = match &self.body {
            None => &empty,
            Some(body) => &body.locals,
        };

        let empty = id_vector::Vector::new();
        let eval_ctx = AstFormatter::new(ty_ctx, fun_ctx, global_ctx, &empty, locals);

        // Use the contexts for printing
        self.gfmt_with_ctx("", &eval_ctx)
    }
}
