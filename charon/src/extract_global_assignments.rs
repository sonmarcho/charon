//! This module extracts globals from operands to put them in a separate let binding.
//! This is done to increase sequentiality of LLBC and reduce the cases to handle
//! in the operands, making the formalisation less complex and easing the functional
//! translation.
//!
//! It also extracts statics fom operands for the same reason, and because we want
//! to treat them as globals in LLBC.
//! To do this, we add a new variable to reference the static:
//! they are accessed by reference in MIR, whereas globals are accessed by value.

use crate::expressions::*;
use crate::im_ast::{iter_function_bodies, iter_global_bodies, make_locals_generator};
use crate::llbc_ast::{FunDecls, GlobalDecls, Statement};
use crate::llbc_ast_utils::transform_operands;
use crate::types::*;
use crate::values::VarId;
use take_mut::take;

fn deref_static_type(ref_ty: &ETy) -> &ETy {
    match ref_ty {
        Ty::Ref(ErasedRegion::Erased, ty, RefKind::Shared) => &*ty,
        _ => unreachable!(
            "expected shared reference for static id type, got {:?}",
            ref_ty
        ),
    }
}

/// If the operand is a constant global identifier, returns an `AssignGlobal` statement
/// that binds a new variable to the global and move it in the operand:
/// `... const X ...`
/// becomes
/// `let x0 = X;`
/// `... move x0 ...`
///
/// If it's a static global identifier, also adds an indirection to take a reference on it:
/// /// `... const X ...`
/// becomes
/// `let x0 = X;`
/// `let x1 = &X;`
/// `... move x1 ...`
fn extract_operand_global_var<F: FnMut(ETy) -> VarId::Id>(
    op: &mut Operand,
    make_new_var: &mut F,
) -> Vec<Statement> {
    let (ty, c) = match op {
        Operand::Const(ty, c) => (ty, c),
        _ => return vec![],
    };
    let (var, new_st) = match *c {
        OperandConstantValue::ConstantValue(_) => return vec![],
        OperandConstantValue::Adt(_, _) => {
            unreachable!("Constant ADTs should have been replaced by now")
        }
        OperandConstantValue::ConstantId(global_id) => {
            let var = make_new_var(ty.clone());
            (var, vec![Statement::AssignGlobal(var, global_id)])
        }
        OperandConstantValue::StaticId(global_id) => {
            let var = make_new_var(deref_static_type(ty).clone());
            let var_ref = make_new_var(ty.clone());
            let rvalue = Rvalue::Ref(Place::new(var), BorrowKind::Shared);
            (
                var_ref,
                vec![
                    Statement::AssignGlobal(var, global_id),
                    Statement::Assign(Place::new(var_ref), rvalue),
                ],
            )
        }
    };
    *op = Operand::Move(Place::new(var));
    return new_st;
}

pub fn transform(funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!("# About to extract global assignments: {name}");

        let mut f = make_locals_generator(&mut b.locals);
        take(&mut b.body, |st| {
            transform_operands(st, &mut |op| extract_operand_global_var(op, &mut f))
        });
    }
}
