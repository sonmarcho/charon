//! In MIR, many binops are desugared into:
//! * for division/modulo: a test that the divider is non zero (making the code
//!   panics if the divider is zero), then the division itself
//! * an operation, followed by a test: typically an addition followed by a check
//!   for overflow
//! This is a bit too low-level for us: we only want to have the binop (which will
//! have a precondition in our theorem prover, or will be monadic...). We thus want
//! to remove those unnecessary checks.

use take_mut::take;

use crate::expressions::*;
use crate::im_ast::{iter_function_bodies, iter_global_bodies};
use crate::llbc_ast::{Assert, FunDecls, GlobalDecls, Statement, SwitchTargets};
use crate::types::*;
use crate::values::*;
use std::iter::FromIterator;

/// Return true iff: `place ++ [pelem] == full_place`
fn check_places_similar_but_last_proj_elem(
    place: &Place,
    pelem: &ProjectionElem,
    full_place: &Place,
) -> bool {
    if place.var_id == full_place.var_id
        && place.projection.len() + 1 == full_place.projection.len()
    {
        for i in 0..place.projection.len() {
            if place.projection[i] != full_place.projection[i] {
                return false;
            }
        }

        return *pelem == full_place.projection[place.projection.len()];
    }
    return false;
}

/// Return true if the binary operation might fail and thus requires its result
/// to be checked (overflows, for instance).
fn binop_requires_assert_after(binop: BinOp) -> bool {
    match binop {
        BinOp::BitXor
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::Eq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Ne
        | BinOp::Ge
        | BinOp::Gt
        | BinOp::Div
        | BinOp::Rem => false,
        BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Shl | BinOp::Shr => true,
    }
}

/// Return true if the unary operation has a precondition (negating the number
/// won't lead to an overflow, for instance).
fn unop_requires_assert_before(unop: UnOp) -> bool {
    match unop {
        UnOp::Not => false,
        UnOp::Neg => true,
        UnOp::Cast(_, _) => {
            // This case is peculiar, because rustc doesn't insert assertions
            // while it can actually fail
            false
        }
    }
}

fn unop_can_fail(unop: UnOp) -> bool {
    match unop {
        UnOp::Not => false,
        UnOp::Neg => true,
        UnOp::Cast(_, _) => {
            // See [unop_requires_assert_before]
            false
        }
    }
}

/// Return true if the binary operation has a precondition (divisor is non zero
/// for instance) and must thus be preceded by an assertion.
fn binop_requires_assert_before(binop: BinOp) -> bool {
    match binop {
        BinOp::BitXor
        | BinOp::BitAnd
        | BinOp::BitOr
        | BinOp::Eq
        | BinOp::Lt
        | BinOp::Le
        | BinOp::Ne
        | BinOp::Ge
        | BinOp::Gt
        | BinOp::Add
        | BinOp::Sub
        | BinOp::Mul
        | BinOp::Shl
        | BinOp::Shr => false,
        BinOp::Div | BinOp::Rem => true,
    }
}

fn binop_can_fail(binop: BinOp) -> bool {
    binop_requires_assert_after(binop) || binop_requires_assert_before(binop)
}

/// Check if this is a group of statements of the form: "check that we can do
/// a unary operation, then do this operation (ex.: check that negating a number
/// won't lead to an overflow)"
fn check_if_assert_then_unop(st1: &Statement, st2: &Statement, st3: &Statement) -> bool {
    match st3 {
        Statement::Assign(_, Rvalue::UnaryOp(unop, _)) => {
            if unop_requires_assert_before(*unop) {
                // We found a unary op with a precondition
                //
                // This group of statements should exactly match the following pattern:
                //   ```
                //   tmp := copy x == const (MIN ...); // `copy x` can be a constant
                //   assert(tmp == false);
                //   dest := -(move x); // `move x` can be a constant
                //   ...
                //   ```
                // If it is note the case, we can't collapse...
                check_if_simplifiable_assert_then_unop(st1, st2, st3)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Make sure the statements match the following pattern:
///   ```
///   tmp := copy x == const (MIN ...); // `copy x` can be a constant
///   assert(tmp == false);
///   dest := -(move x); // `move x` can be a constant
///   ...
///   ```
/// Or that there is no assert but the value is a constant which will not
/// lead to saturation.
fn check_if_simplifiable_assert_then_unop(
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match (st1, st2, st3) {
        (
            Statement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    op,
                    Operand::Const(
                        _,
                        OperandConstantValue::ConstantValue(ConstantValue::Scalar(saturated)),
                    ),
                ),
            ),
            Statement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            Statement::Assign(_mp, Rvalue::UnaryOp(unop, op1)),
        ) => {
            // Case 1: pattern with assertion
            assert!(*unop == UnOp::Neg);
            assert!(!(*expected));

            assert!(eq_dest == cond_op);

            // Check the two operands:
            // - either they are (copy, move)
            // - or they are the same constant
            match (op, op1) {
                (Operand::Copy(p), Operand::Move(p1)) => assert!(p == p1),
                (Operand::Const(_, cv), Operand::Const(_, cv1)) => assert!(cv == cv1),
                _ => unreachable!(),
            }

            assert!(saturated.is_int() && saturated.is_min());
            true
        }
        (
            _,
            _,
            Statement::Assign(
                _mp,
                Rvalue::UnaryOp(
                    unop,
                    Operand::Const(
                        _,
                        OperandConstantValue::ConstantValue(ConstantValue::Scalar(value)),
                    ),
                ),
            ),
        ) => {
            assert!(*unop == UnOp::Neg);
            // Case 2: no assertion to check that there will not be an overflow:
            // the value must be a constant which will not lead to an overflow.
            assert!(value.is_int() && !value.is_min());
            false
        }
        _ => {
            unreachable!();
        }
    }
}

/// Simplify patterns of the form:
///   ```
///   tmp := copy x == const (MIN ...); // `copy x` can be a constant
///   assert(tmp == false);
///   dest := -(move x); // `move x` can be a constant
///   ...
///   ```
/// to:
///   ```
///   dest := -(move x); // `move x` can be a constant
///   ...
///   ```
fn simplify_assert_then_unop(_st1: Statement, _st2: Statement, st3: Statement) -> Statement {
    st3
}

/// Check if this is a group of statements of the form:
/// - do an operation,
/// - check it succeeded (didn't overflow, etc.)
/// - retrieve the value
///   ```
///   ```
/// Check if this is a group of statements which should be collapsed to a
/// single checked binop.
/// Simply check if the first statements is a checked binop.
fn check_if_binop_then_assert(st1: &Statement, st2: &Statement, st3: &Statement) -> bool {
    match st1 {
        Statement::Assign(_, Rvalue::BinaryOp(binop, _, _)) => {
            if binop_requires_assert_after(*binop) {
                // We found a checked binary op.
                //
                // This group of statements should exactly match the following pattern:
                //   ```
                //   tmp := copy x + copy y; // Possibly a different binop
                //   assert(move (tmp.1) == false);
                //   dest := move (tmp.0);
                //   ...
                //   ```
                // If it is note the case, we can't collapse...
                check_if_simplifiable_binop_then_assert(st1, st2, st3);
                true
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Make sure the statements match the following pattern:
///   ```
///   tmp := op1 + op2; // Possibly a different binop
///   assert(move (tmp.1) == false);
///   dest := move (tmp.0);
///   ...
///   ```
fn check_if_simplifiable_binop_then_assert(st1: &Statement, st2: &Statement, st3: &Statement) {
    match (st1, st2, st3) {
        (
            Statement::Assign(bp, Rvalue::BinaryOp(binop, _op1, _op2)),
            Statement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            Statement::Assign(_mp, Rvalue::Use(Operand::Move(mr))),
        ) => {
            assert!(binop_requires_assert_after(*binop));
            assert!(!(*expected));

            // We must have:
            // cond_op == bp.1
            // mr == bp.0
            let check1 = check_places_similar_but_last_proj_elem(
                bp,
                &ProjectionElem::Field(FieldProjKind::Tuple(2), FieldId::Id::new(1)),
                cond_op,
            );
            assert!(check1);

            let check2 = check_places_similar_but_last_proj_elem(
                bp,
                &ProjectionElem::Field(FieldProjKind::Tuple(2), FieldId::Id::new(0)),
                mr,
            );
            assert!(check2);
        }
        _ => {
            unreachable!();
        }
    }
}

/// Simplify patterns of the form:
///   ```
///   tmp := op1 + op2; // Possibly a different binop
///   assert(move (tmp.1) == false);
///   dest := move (tmp.0);
///   ...
///   ```
/// to:
///   ```
///   tmp := copy x + copy y; // Possibly a different binop
///   ...
///   ```
/// Note that the type of the binop changes in the two situations (in the
/// translation, before the transformation `+` returns a pair (bool, int),
/// after it has a monadic type).
fn simplify_binop_then_assert(st1: Statement, st2: Statement, st3: Statement) -> Statement {
    match (st1, st2, st3) {
        (Statement::Assign(_, binop), Statement::Assert(_), Statement::Assign(mp, _)) => {
            return Statement::Assign(mp, binop);
        }
        _ => {
            unreachable!();
        }
    }
}

/// Check if this is a group of statements of the form: "check that we can do
/// an binary operation, then do this operation (ex.: check that a divisor is
/// non zero before doing a division, panic otherwise)"
fn check_if_assert_then_binop(st1: &Statement, st2: &Statement, st3: &Statement) -> bool {
    match st3 {
        Statement::Assign(_, Rvalue::BinaryOp(binop, _, _)) => {
            if binop_requires_assert_before(*binop) {
                // We found an unchecked binop which should be simplified (division
                // or remainder computation).
                //
                // There are two situations:
                // - if the divisor is a non-zero constant, rust may not insert
                //   an assertion (because it can statically check it)
                // - otherwise, the group of statements must match the following
                //   pattern exactly:
                //   ```
                //   tmp := (copy divisor) == 0;
                //   assert((move tmp) == false);
                //   dest := move dividend / move divisor; // Can also be a `%`
                //   ...
                //   ```
                //
                //   Or this pattern:
                //   ```
                //   tmp := (constant_divisor) == 0;
                //   assert((move tmp) == false);
                //   dest := move dividend / constant_divisor; // Can also be a `%`
                //   ...
                //   ```
                check_if_simplifiable_assert_then_binop(st1, st2, st3)
            } else {
                false
            }
        }
        _ => false,
    }
}

/// Make sure the statements match the following pattern:
///   ```
///   tmp := (copy divisor) == 0;
///   assert((move tmp) == false);
///   dest := move dividend / move divisor; // Can also be a `%`
///   ...
///   ```
/// Or that there is no assert but the divisor is a non-zero constant.
fn check_if_simplifiable_assert_then_binop(
    st1: &Statement,
    st2: &Statement,
    st3: &Statement,
) -> bool {
    match (st1, st2, st3) {
        (
            Statement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    Operand::Copy(eq_op1),
                    Operand::Const(
                        _,
                        OperandConstantValue::ConstantValue(ConstantValue::Scalar(zero)),
                    ),
                ),
            ),
            Statement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            Statement::Assign(_mp, Rvalue::BinaryOp(binop, _dividend, Operand::Move(divisor))),
        ) => {
            // Case 1: pattern with copy/move and assertion
            assert!(binop_requires_assert_before(*binop));
            assert!(!(*expected));
            assert!(eq_op1 == divisor);
            assert!(eq_dest == cond_op);
            if zero.is_int() {
                assert!(zero.as_int().unwrap() == 0);
            } else {
                assert!(zero.as_uint().unwrap() == 0);
            }
            true
        }
        (
            Statement::Assign(
                eq_dest,
                Rvalue::BinaryOp(
                    BinOp::Eq,
                    divisor,
                    Operand::Const(
                        _,
                        OperandConstantValue::ConstantValue(ConstantValue::Scalar(zero)),
                    ),
                ),
            ),
            Statement::Assert(Assert {
                cond: Operand::Move(cond_op),
                expected,
            }),
            Statement::Assign(_mp, Rvalue::BinaryOp(binop, _dividend, divisor1)),
        ) => {
            // Case 2: pattern with constant divisor and assertion
            assert!(binop_requires_assert_before(*binop));
            assert!(!(*expected));
            assert!(divisor.is_const());
            match divisor {
                Operand::Const(
                    _,
                    OperandConstantValue::ConstantValue(ConstantValue::Scalar(_)),
                ) => (),
                _ => unreachable!(),
            }
            assert!(divisor1 == divisor);
            assert!(eq_dest == cond_op);
            // Check that the zero is zero
            if zero.is_int() {
                assert!(zero.as_int().unwrap() == 0);
            } else {
                assert!(zero.as_uint().unwrap() == 0);
            }
            true
        }
        (_, _, Statement::Assign(_mp, Rvalue::BinaryOp(_, _, Operand::Const(_, divisor)))) => {
            // Case 3: no assertion to check the divisor != 0, the divisor must be a
            // non-zero constant
            let cv = divisor.as_constant_value();
            let cv = cv.as_scalar();
            if cv.is_uint() {
                assert!(cv.as_uint().unwrap() != 0)
            } else {
                assert!(cv.as_int().unwrap() != 0)
            };
            false
        }
        _ => {
            unreachable!();
        }
    }
}

/// Simplify patterns of the form:
///   ```
///   tmp := (copy divisor) == 0;
///   assert((move tmp) == false);
///   dest := move dividend / move divisor; // Can also be a `%`
///   ...
///   ```
/// to:
///   ```
///   dest := move dividend / move divisor; // Can also be a `%`
///   ...
///   ```
fn simplify_assert_then_binop(_st1: Statement, _st2: Statement, st3: Statement) -> Statement {
    st3
}

/// Attempt to simplify a sequence of statemnets
fn simplify_st_seq(
    st1: Statement,
    st2: Statement,
    st3: Statement,
    st4: Option<Statement>,
) -> Statement {
    // Try to simplify
    let simpl_st = {
        // Simplify checked unops (negation)
        if check_if_assert_then_unop(&st1, &st2, &st3) {
            simplify_assert_then_unop(st1, st2, st3)
        }
        // Simplify checked binops
        else if check_if_binop_then_assert(&st1, &st2, &st3) {
            simplify_binop_then_assert(st1, st2, st3)
        }
        // Simplify unchecked binops (division, modulo)
        else if check_if_assert_then_binop(&st1, &st2, &st3) {
            simplify_assert_then_binop(st1, st2, st3)
        } else {
            // Not simplifyable
            let next_st = match st4 {
                Option::Some(st4) => Statement::Sequence(Box::new(st3), Box::new(st4)),
                Option::None => st3,
            };
            let next_st = Statement::Sequence(Box::new(st2), Box::new(next_st));
            return Statement::Sequence(Box::new(simplify_st(st1)), Box::new(simplify_st(next_st)));
        }
    };

    // Combine the simplified statements with the statement after, if there is
    match st4 {
        Option::Some(st4) => {
            let st4 = simplify_st(st4);
            return Statement::Sequence(Box::new(simpl_st), Box::new(st4));
        }
        Option::None => return simpl_st,
    }
}

fn simplify_st(st: Statement) -> Statement {
    match st {
        Statement::Assign(p, rv) => {
            // Check that we never failed to simplify a binop
            match &rv {
                Rvalue::BinaryOp(binop, _, divisor) => {
                    // If it is an unsimplified binop, it must be / or %
                    // and the divisor must be a non-zero constant
                    if binop_can_fail(*binop) {
                        match binop {
                            BinOp::Div | BinOp::Rem => {
                                let (_, cv) = divisor.as_const();
                                let cv = cv.as_constant_value();
                                let cv = cv.as_scalar();
                                if cv.is_uint() {
                                    assert!(cv.as_uint().unwrap() != 0)
                                } else {
                                    assert!(cv.as_int().unwrap() != 0)
                                };
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                }
                Rvalue::UnaryOp(unop, v) => {
                    // If it is an unsimplified unop which can fail, it must be
                    // the negation, and the value must be a constant which won't
                    // lead to overflow.
                    if unop_can_fail(*unop) {
                        match unop {
                            UnOp::Neg => {
                                let (_, cv) = v.as_const();
                                let cv = cv.as_constant_value();
                                let cv = cv.as_scalar();
                                assert!(cv.is_int());
                                assert!(!cv.is_min());
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                }
                _ => (),
            }
            Statement::Assign(p, rv)
        }
        Statement::AssignGlobal(id, gid) => Statement::AssignGlobal(id, gid),
        Statement::FakeRead(p) => Statement::FakeRead(p),
        Statement::SetDiscriminant(p, vid) => Statement::SetDiscriminant(p, vid),
        Statement::Drop(p) => Statement::Drop(p),
        Statement::Assert(assert) => Statement::Assert(assert),
        Statement::Call(call) => Statement::Call(call),
        Statement::Panic => Statement::Panic,
        Statement::Return => Statement::Return,
        Statement::Break(i) => Statement::Break(i),
        Statement::Continue(i) => Statement::Continue(i),
        Statement::Nop => Statement::Nop,
        Statement::Switch(op, targets) => {
            let targets = match targets {
                SwitchTargets::If(st1, st2) => {
                    SwitchTargets::If(Box::new(simplify_st(*st1)), Box::new(simplify_st(*st2)))
                }
                SwitchTargets::SwitchInt(int_ty, targets, otherwise) => {
                    let targets =
                        Vec::from_iter(targets.into_iter().map(|(v, e)| (v, simplify_st(e))));
                    let otherwise = simplify_st(*otherwise);
                    SwitchTargets::SwitchInt(int_ty, targets, Box::new(otherwise))
                }
            };
            Statement::Switch(op, targets)
        }
        Statement::Loop(loop_body) => Statement::Loop(Box::new(simplify_st(*loop_body))),
        Statement::Sequence(st1, st2) => match *st2 {
            Statement::Sequence(st2, st3) => match *st3 {
                Statement::Sequence(st3, st4) => {
                    simplify_st_seq(*st1, *st2, *st3, Option::Some(*st4))
                }
                st3 => simplify_st_seq(*st1, *st2, st3, Option::None),
            },
            st2 => Statement::Sequence(Box::new(simplify_st(*st1)), Box::new(simplify_st(st2))),
        },
    }
}

pub fn simplify(funs: &mut FunDecls, globals: &mut GlobalDecls) {
    for (name, b) in iter_function_bodies(funs).chain(iter_global_bodies(globals)) {
        trace!("# About to simplify operands: {name}");
        take(&mut b.body, simplify_st);
    }
}
