//! Implements expressions: paths, operands, rvalues, lvalues

pub use crate::expressions_utils::*;
use crate::im_ast::GlobalDeclId;
use crate::types::*;
use crate::values::*;
use im::Vector;
use macros::{EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use serde::Serialize;

#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Place {
    pub var_id: VarId::Id,
    pub projection: Projection,
}

pub type Projection = Vector<ProjectionElem>;

/// Note that we don't have the equivalent of "downcasts".
/// Downcasts are actually necessary, for instance when initializing enumeration
/// values: the value is initially `Bottom`, and we need a way of knowing the
/// variant.
/// For example:
/// `((_0 as Right).0: T2) = move _1;`
/// In MIR, downcasts always happen before field projections: in our internal
/// language, we thus merge downcasts and field projections.
#[derive(Debug, PartialEq, Eq, Clone, VariantName, Serialize)]
pub enum ProjectionElem {
    /// Dereference a shared/mutable reference.
    Deref,
    /// Dereference a boxed value.
    /// Note that this doesn't exist in MIR where `Deref` is used both for the
    /// mutable and shared references *and* the boxed values. As semantically we
    /// don't handle those two cases the same way at all, we disambiguate them
    /// during the translation.
    /// In rust, this comes from the `*` operator applied on boxes.
    DerefBox,
    /// Projection from ADTs (variants, structures).
    /// We allow projections to be used as left-values and right-values.
    /// We should never have projections to fields of symbolic variants (they
    /// should have been expanded before through a match).
    /// Note that in MIR, field projections don't contain any type information
    /// (adt identifier, variant id, etc.). This information can be valuable
    /// (for pretty printing for instance). We retrieve it through
    /// type-checking.
    Field(FieldProjKind, FieldId::Id),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum FieldProjKind {
    #[serde(rename = "ProjAdt")]
    Adt(TypeDeclId::Id, Option<VariantId::Id>),
    /// The option type is assumed (it comes from the standard library)
    #[serde(rename = "ProjOption")]
    Option(VariantId::Id),
    /// If we project from a tuple, the projection kind gives the arity of the
    #[serde(rename = "ProjTuple")]
    Tuple(usize),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum BorrowKind {
    Shared,
    Mut,
    TwoPhaseMut,
}

/// Unary operation
#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, VariantName, Serialize)]
pub enum UnOp {
    Not,
    /// This can overflow. In practice, rust introduces an assert before
    /// (in debug mode) to check that it is not equal to the minimum integer
    /// value (for the proper type).
    Neg,
    /// Casts are rvalues in MIR, but we treat them as unops. For now, we
    /// only support for integer to integer, but we can also do from integers/booleans
    /// to integers/booleans. For now, we don't handle pointer casts.
    ///
    /// The first integer type gives the source type, the second one gives
    /// the destination type.
    Cast(IntegerTy, IntegerTy),
}

/// Binary operations.
#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, VariantName, Serialize)]
pub enum BinOp {
    BitXor,
    BitAnd,
    BitOr,
    Eq,
    Lt,
    Le,
    Ne,
    Ge,
    Gt,
    /// Can fail if the divisor is 0.
    Div,
    /// Can fail if the divisor is 0.
    Rem,
    /// Can overflow
    Add,
    /// Can overflow
    Sub,
    /// Can overflow
    Mul,
    /// Can fail if the shift is too big
    Shl,
    /// Can fail if the shift is too big
    Shr,
    // No Offset binary operation: this is an operation on raw pointers
}

/// The constructors match printed MIR operand prefixes (e.g. `const 2`).
#[derive(Debug, PartialEq, Eq, Clone, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum Operand {
    Copy(Place),
    Move(Place),
    /// Constant value (including constant and static variables)
    Const(ETy, OperandConstantValue),
}

/// Constant value for an operand.
/// Only the `ConstantValue` case is remaining in LLBC final form.
///
/// The other cases come from a straight translation from the MIR:
///
/// `Adt` case:
/// It is a bit annoying, but rustc treats some ADT and tuple instances as
/// constants when generating MIR:
/// - an enumeration with one variant and no fields is a constant.
/// - a structure with no field is a constant.
/// - sometimes, Rust stores the initialization of an ADT as a constant
///   (if all the fields are constant) rather than as an aggregated value
/// It is translated to regular ADTs, see [regularize_constant_adts.rs].
///
/// `Identifier` and `Static` case:
/// Match constant variables. Their access will be done elsewhere in a
/// separate statement, see [extract_global_assignments.rs].
#[derive(Debug, PartialEq, Eq, Clone, VariantName, EnumIsA, EnumAsGetters, VariantIndexArity)]
pub enum OperandConstantValue {
    ConstantValue(ConstantValue),
    ///
    /// In most situations:
    /// Enumeration with one variant with no fields, structure with
    /// no fields, unit (encoded as a 0-tuple).
    ///
    /// Less frequently: arbitrary ADT values.
    Adt(Option<VariantId::Id>, Vector<OperandConstantValue>),
    ///
    /// The case when the constant is elsewhere.
    /// The MIR seems to forbid more complex expressions like paths :
    /// Reading the constant a.b is translated to { _1 = const a; _2 = (_1.0) }.
    ConstantId(GlobalDeclId::Id),
    ///
    /// Same as for constants, except that statics are accessed through references.
    StaticId(GlobalDeclId::Id),
}

#[derive(Debug, Clone, Serialize)]
pub enum Rvalue {
    Use(Operand),
    Ref(Place, BorrowKind),
    /// Unary operation (not, neg)
    UnaryOp(UnOp, Operand),
    /// Binary operations (note that we merge "checked" and "unchecked" binops)
    BinaryOp(BinOp, Operand, Operand),
    /// Discriminant (for enumerations).
    /// Note that discriminant values have type isize
    Discriminant(Place),
    /// Creates an aggregate value, like a tuple, a struct or an enum:
    /// ```
    /// l = List::Cons { value:x, tail:tl };
    /// ```
    /// Note that in some MIR passes (like optimized MIR), aggregate values are
    /// decomposed, like below:
    /// ```
    /// (l as List::Cons).value = x;
    /// (l as List::Cons).tail = tl;
    /// ```
    /// Because we may want to plug our translation mechanism at various
    /// places, we need to take both into accounts in the translation and in
    /// our semantics. Aggregate value initialization is easy, you might want
    /// to have a look at expansion of `Bottom` values for explanations about the
    /// other case.
    Aggregate(AggregateKind, Vec<Operand>),
}

#[derive(Debug, Clone)]
pub enum AggregateKind {
    Tuple,
    // TODO: treat Option in a general manner (we should extract the definitions
    // of the external enumerations - because as they are public, their variants are
    // public)
    Option(VariantId::Id, ETy),
    Adt(
        TypeDeclId::Id,
        Option<VariantId::Id>,
        Vec<ErasedRegion>,
        Vec<ETy>,
    ),
}
