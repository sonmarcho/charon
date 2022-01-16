#![allow(dead_code)]

use crate::common::*;
use crate::formatter::Formatter;
use crate::id_vector;
use crate::vars::*;
use im::{HashMap, OrdSet, Vector};
use macros::{generate_index_type, EnumAsGetters, EnumIsA, VariantIndexArity, VariantName};
use rustc_middle::ty::{IntTy, UintTy};
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};

pub type FieldName = String;

// We need to manipulate a lot of indices for the types, variables, definitions,
// etc. In order not to confuse them, we define an index type for every one of
// them (which is just a struct with a unique usize field), together with some
// utilities like a fresh index generator. Those structures and utilities are
// generated by using macros.
generate_index_type!(TypeVarId);
generate_index_type!(TypeDefId);
generate_index_type!(VariantId);
generate_index_type!(FieldId);
generate_index_type!(RegionVarId);

/// Type variable.
/// We make sure not to mix variables and type variables by having two distinct
/// definitions.
#[derive(Debug, Clone, Serialize)]
pub struct TypeVar {
    /// Unique index identifying the variable
    pub index: TypeVarId::Id,
    /// Variable name
    pub name: String,
}

/// Region variable.
#[derive(Debug, Clone, Serialize)]
pub struct RegionVar {
    /// Unique index identifying the variable
    pub index: RegionVarId::Id,
    /// Region name
    pub name: Option<String>,
}

/// Region as used in afunction's signatures (in which case we use region variable
/// ids) and in symbolic variables and projections (in which case we use region
/// ids).
#[derive(
    Debug, PartialEq, Eq, Clone, Copy, Hash, PartialOrd, Ord, EnumIsA, EnumAsGetters, Serialize,
)]
pub enum Region<Rid: Copy + Eq> {
    /// Static region
    Static,
    /// Non-static region.
    Var(Rid),
}

/// The type of erased regions. See [`Ty`](Ty) for more explanations.
/// We could use `()`, but having a dedicated type makes things more explicit.
#[derive(Debug, PartialEq, Eq, Clone, Copy, Serialize)]
pub enum ErasedRegion {
    Erased,
}

/// A type definition.
/// Can only be an ADT (structure or enumeration), as type aliases are inlined
/// in MIR.
#[derive(Debug, Clone, Serialize)]
pub struct TypeDef {
    pub def_id: TypeDefId::Id,
    pub name: Name,
    pub region_params: RegionVarId::Vector<RegionVar>,
    pub type_params: TypeVarId::Vector<TypeVar>,
    pub kind: TypeDefKind,
    // The lifetime's hierarchy between the different regions.
    //pub regions_hierarchy: RegionGroups,
}

#[derive(Debug, Clone, EnumIsA, EnumAsGetters, Serialize)]
pub enum TypeDefKind {
    Struct(FieldId::Vector<Field>),
    Enum(VariantId::Vector<Variant>),
}

#[derive(Debug, Clone, Serialize)]
pub struct Variant {
    pub name: String,
    pub fields: FieldId::Vector<Field>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Field {
    pub name: String,
    pub ty: RTy,
}

#[derive(Debug, PartialEq, Eq, Copy, Clone, EnumIsA, VariantName, Serialize)]
pub enum IntegerTy {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, VariantName, EnumIsA, Serialize)]
pub enum RefKind {
    Mut,
    Shared,
}

/// Type identifier.
///
/// Allows us to factorize the code for assumed types, adts and tuples
#[derive(Debug, PartialEq, Eq, Clone, Copy, VariantName, EnumAsGetters, EnumIsA, Serialize)]
pub enum TypeId {
    Adt(TypeDefId::Id),
    Tuple,
    /// Assumed type. A non-primitive type coming from a standard library
    /// and that we handle like a primitive type. Types falling into this
    /// category include: Box, Vec, Cell...
    Assumed(AssumedTy),
}

/// A type.
///
/// Types are parameterized by a type parameter used for regions (or lifetimes).
/// The reason is that in MIR, regions are used in the function signatures but
/// are erased in the function bodies. We make this extremely explicit (and less
/// error prone) in our encoding by using two different types: [`Region`](Region)
/// and [`ErasedRegion`](ErasedRegion), the latter being an enumeration with only
/// one variant.
#[derive(Debug, PartialEq, Eq, Clone, VariantName, EnumIsA, EnumAsGetters, VariantIndexArity)]
pub enum Ty<R>
where
    R: Clone + std::cmp::Eq,
{
    /// An ADT.
    /// Note that here ADTs are very general. They can be:
    /// - user-defined ADTs
    /// - tuples (including `unit`, which is a 0-tuple)
    /// - assumed types
    /// The information on the nature of the ADT is stored in (`TypeId`)[TypeId].
    Adt(TypeId, Vector<R>, Vector<Ty<R>>),
    TypeVar(TypeVarId::Id),
    Bool,
    Char,
    /// The never type, for computations which don't return. It is sometimes
    /// necessary for intermediate variables. For instance, if we do (coming
    /// from the rust documentation):
    /// ```
    /// let num: u32 = match get_a_number() {
    ///     Some(num) => num,
    ///     None => break,
    /// };
    /// ```
    /// the second branch will have type `Never`. Also note that `Never`
    /// can be coerced to any type.
    /// TODO: but do we really use this type for variables?...
    Never,
    Integer(IntegerTy),
    // We don't support floating point numbers on purpose
    Str,
    // TODO: there should be a constant with the array
    Array(Box<Ty<R>>),
    Slice(Box<Ty<R>>),
    /// A borrow
    Ref(R, Box<Ty<R>>, RefKind),
}

/// Type with *R*egions.
///
/// Used in function signatures and type definitions.
/// TODO: rename to sty (*signature* type). Region types are used by the
/// interpreter.
pub type RTy = Ty<Region<RegionVarId::Id>>;

/// Type with *E*rased regions.
///
/// Used in function bodies, "general" value types, etc.
pub type ETy = Ty<ErasedRegion>;

/// Assumed types identifiers.
///
/// WARNING: for now, all the assumed types are covariant in the generic
/// parameters (if there are). Adding types which don't satisfy this
/// will require to update the code abstracting the signatures (to properly
/// take into account the lifetime constraints).
#[derive(Debug, PartialEq, Eq, Clone, Copy, EnumIsA, EnumAsGetters, VariantName, Serialize)]
pub enum AssumedTy {
    /// Boxes have a special treatment: we translate them as identity.
    Box,
    // TODO: Vec
}

pub type RegionSubst<R> = HashMap<RegionVarId::Id, R>;
pub type TypeSubst<R> = HashMap<TypeVarId::Id, Ty<R>>;
/// Type substitution where the regions are erased
pub type ETypeSubst = TypeSubst<ErasedRegion>;

impl RegionVarId::Id {
    pub fn substitute<R>(&self, rsubst: &RegionSubst<R>) -> R
    where
        R: Clone,
    {
        rsubst.get(self).unwrap().clone()
    }
}

impl<Rid: Copy + Eq> Region<Rid> {
    pub fn fmt_with_ctx<T>(&self, ctx: &T) -> String
    where
        T: Formatter<Rid>,
    {
        match self {
            Region::Static => "'static".to_string(),
            Region::Var(id) => ctx.format_object(*id),
        }
    }
}

impl<Rid1: Copy + Eq + Ord + std::hash::Hash> Region<Rid1> {
    pub fn substitute<Rid2: Copy + Eq>(
        &self,
        rsubst: &HashMap<Rid1, Region<Rid2>>,
    ) -> Region<Rid2> {
        match self {
            Region::Static => Region::Static,
            Region::Var(id) => rsubst.get(id).unwrap().clone(),
        }
    }

    pub fn contains_var(&self, rset: &OrdSet<Rid1>) -> bool {
        match self {
            Region::Static => false,
            Region::Var(id) => rset.contains(id),
        }
    }
}

/// Type context.
/// Contains type definitions and function signatures.
#[derive(Clone)]
pub struct TypeDefs {
    pub types: TypeDefId::Vector<TypeDef>,
}

/*
 * Implementations, traits
 */

impl TypeVar {
    pub fn new(index: TypeVarId::Id, name: String) -> TypeVar {
        TypeVar {
            index: index,
            name: name,
        }
    }

    pub fn fresh(name: String, gen: &mut TypeVarId::Generator) -> TypeVar {
        TypeVar {
            index: gen.fresh_id(),
            name: name,
        }
    }
}

impl std::string::ToString for TypeVar {
    fn to_string(&self) -> String {
        format!("{}", self.name).to_owned()
    }
}

impl std::string::ToString for RegionVar {
    fn to_string(&self) -> String {
        let id = region_var_id_to_pretty_string(self.index);
        match &self.name {
            Some(name) => format!("{}", name).to_owned(),
            None => format!("{}", id).to_owned(),
        }
    }
}

impl TypeDef {
    /// The variant id should be `None` if it is a structure and `Some` if it
    /// is an enumeration.
    pub fn get_fields(&self, variant_id: Option<VariantId::Id>) -> &FieldId::Vector<Field> {
        match &self.kind {
            TypeDefKind::Enum(variants) => &variants.get(variant_id.unwrap()).unwrap().fields,
            TypeDefKind::Struct(fields) => {
                assert!(variant_id.is_none());
                fields
            }
        }
    }

    /// The variant id should be `None` if it is a structure and `Some` if it
    /// is an enumeration.
    pub fn get_erased_regions_instantiated_field_types(
        &self,
        variant_id: Option<VariantId::Id>,
        inst_types: &Vector<ETy>,
    ) -> Vector<ETy> {
        // Introduce the substitution
        let ty_subst = make_type_subst(self.type_params.iter().map(|x| x.index), inst_types.iter());

        let fields = self.get_fields(variant_id);
        let field_types: Vec<ETy> = fields
            .iter()
            .map(|f| f.ty.erase_regions_substitute_types(&ty_subst))
            .collect();

        Vector::from(field_types)
    }

    /// The variant id should be `None` if it is a structure and `Some` if it
    /// is an enumeration.
    pub fn get_erased_regions_instantiated_field_type(
        &self,
        variant_id: Option<VariantId::Id>,
        inst_types: &Vector<ETy>,
        field_id: FieldId::Id,
    ) -> ETy {
        // Introduce the substitution
        let ty_subst = make_type_subst(self.type_params.iter().map(|x| x.index), inst_types.iter());

        let fields = self.get_fields(variant_id);
        let field_type = fields
            .get(field_id)
            .unwrap()
            .ty
            .erase_regions()
            .substitute_types(&ty_subst);
        field_type
    }

    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDefId::Id>,
    {
        let params = TypeDef::fmt_params(&self.region_params, &self.type_params);
        match &self.kind {
            TypeDefKind::Struct(fields) => {
                if fields.len() > 0 {
                    let fields: Vec<String> = fields
                        .iter()
                        .map(|f| format!("\n  {}", f.fmt_with_ctx(ctx)).to_owned())
                        .collect();
                    let fields = fields.join(",");
                    format!(
                        "struct {}{} = {{{}\n}}",
                        self.name.to_string(),
                        params,
                        fields
                    )
                    .to_owned()
                } else {
                    format!("struct {}{} = {{}}", self.name.to_string(), params).to_owned()
                }
            }
            TypeDefKind::Enum(variants) => {
                let variants: Vec<String> = variants
                    .iter()
                    .map(|v| format!("|  {}", v.fmt_with_ctx(ctx)).to_owned())
                    .collect();
                let variants = variants.join("\n");
                format!("enum {}{} =\n{}", self.name.to_string(), params, variants).to_owned()
            }
        }
    }

    fn fmt_params(
        region_params: &RegionVarId::Vector<RegionVar>,
        type_params: &TypeVarId::Vector<TypeVar>,
    ) -> String {
        if region_params.len() + type_params.len() > 0 {
            let regions = region_params.iter().map(|r| r.to_string());
            let type_params = type_params.iter().map(|p| p.to_string());
            let params: Vec<String> = regions.chain(type_params).collect();
            format!("<{}>", params.join(", ")).to_owned()
        } else {
            "".to_string()
        }
    }
}

impl std::string::ToString for TypeDef {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl Variant {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDefId::Id>,
    {
        let fields: Vec<String> = self.fields.iter().map(|f| f.fmt_with_ctx(ctx)).collect();
        let fields = fields.join(", ");
        format!("{}({})", self.name, fields).to_owned()
    }
}

impl Field {
    pub fn fmt_with_ctx<'a, T>(&'a self, ctx: &'a T) -> String
    where
        T: Formatter<TypeVarId::Id>
            + Formatter<RegionVarId::Id>
            + Formatter<&'a Region<RegionVarId::Id>>
            + Formatter<TypeDefId::Id>,
    {
        format!("{}: {}", self.name, self.ty.fmt_with_ctx(ctx)).to_owned()
    }
}

impl std::string::ToString for Variant {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl std::string::ToString for Field {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl IntegerTy {
    pub fn rust_int_ty_to_integer_ty(ty: IntTy) -> IntegerTy {
        match ty {
            IntTy::Isize => IntegerTy::Isize,
            IntTy::I8 => IntegerTy::I8,
            IntTy::I16 => IntegerTy::I16,
            IntTy::I32 => IntegerTy::I32,
            IntTy::I64 => IntegerTy::I64,
            IntTy::I128 => IntegerTy::I128,
        }
    }

    pub fn rust_uint_ty_to_integer_ty(ty: UintTy) -> IntegerTy {
        match ty {
            UintTy::Usize => IntegerTy::Usize,
            UintTy::U8 => IntegerTy::U8,
            UintTy::U16 => IntegerTy::U16,
            UintTy::U32 => IntegerTy::U32,
            UintTy::U64 => IntegerTy::U64,
            UintTy::U128 => IntegerTy::U128,
        }
    }

    pub fn is_signed(&self) -> bool {
        match self {
            IntegerTy::Isize
            | IntegerTy::I8
            | IntegerTy::I16
            | IntegerTy::I32
            | IntegerTy::I64
            | IntegerTy::I128 => true,
            _ => false,
        }
    }

    pub fn is_unsigned(&self) -> bool {
        !(self.is_signed())
    }
}

pub fn type_def_id_to_pretty_string(id: TypeDefId::Id) -> String {
    format!("@Adt{}", id).to_owned()
}

pub fn region_var_id_to_pretty_string(id: RegionVarId::Id) -> String {
    format!("@R{}", id.to_string()).to_owned()
}

pub fn integer_ty_to_string(ty: IntegerTy) -> String {
    match ty {
        IntegerTy::Isize => "isize".to_owned(),
        IntegerTy::I8 => "i8".to_owned(),
        IntegerTy::I16 => "i16".to_owned(),
        IntegerTy::I32 => "i32".to_owned(),
        IntegerTy::I64 => "i64".to_owned(),
        IntegerTy::I128 => "i128".to_owned(),
        IntegerTy::Usize => "usize".to_owned(),
        IntegerTy::U8 => "u8".to_owned(),
        IntegerTy::U16 => "u16".to_owned(),
        IntegerTy::U32 => "u32".to_owned(),
        IntegerTy::U64 => "u64".to_owned(),
        IntegerTy::U128 => "u128".to_owned(),
    }
}

pub fn intty_to_string(ty: IntTy) -> String {
    match ty {
        IntTy::Isize => "isize".to_owned(),
        IntTy::I8 => "i8".to_owned(),
        IntTy::I16 => "i16".to_owned(),
        IntTy::I32 => "i32".to_owned(),
        IntTy::I64 => "i64".to_owned(),
        IntTy::I128 => "i128".to_owned(),
    }
}

fn uintty_to_string(ty: UintTy) -> String {
    match ty {
        UintTy::Usize => "usize".to_owned(),
        UintTy::U8 => "u8".to_owned(),
        UintTy::U16 => "u16".to_owned(),
        UintTy::U32 => "u32".to_owned(),
        UintTy::U64 => "u64".to_owned(),
        UintTy::U128 => "u128".to_owned(),
    }
}

impl TypeId {
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        T: Formatter<TypeDefId::Id>,
    {
        match self {
            TypeId::Tuple => "".to_string(),
            TypeId::Adt(def_id) => ctx.format_object(*def_id),
            TypeId::Assumed(aty) => match aty {
                AssumedTy::Box => "std::boxed::Box".to_string(),
            },
        }
    }
}

impl<R> Ty<R>
where
    R: Clone + Eq,
{
    /// Return true if it is actually unit (i.e.: 0-tuple)
    pub fn is_unit(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Tuple, regions, tys) => {
                assert!(regions.is_empty());
                tys.is_empty()
            }
            _ => false,
        }
    }

    /// Return the unit type
    pub fn mk_unit() -> Ty<R> {
        Ty::Adt(TypeId::Tuple, Vector::new(), Vector::new())
    }

    /// Return true if this is a scalar type
    pub fn is_scalar(&self) -> bool {
        self.is_integer()
    }

    pub fn is_unsigned_scalar(&self) -> bool {
        match self {
            Ty::Integer(kind) => kind.is_unsigned(),
            _ => false,
        }
    }

    pub fn is_signed_scalar(&self) -> bool {
        match self {
            Ty::Integer(kind) => kind.is_signed(),
            _ => false,
        }
    }

    /// Is the type a leaf type (without children)?
    /// - true if bool, char, var...
    /// - false if adt, array...
    pub fn is_leaf(&self) -> bool {
        match self {
            Ty::Adt(_, _, _) | Ty::Array(_) | Ty::Slice(_) | Ty::Ref(_, _, _) => false,
            Ty::TypeVar(_) | Ty::Bool | Ty::Char | Ty::Never | Ty::Integer(_) | Ty::Str => true,
        }
    }

    /// Format the type as a string.
    ///
    /// We take an optional type context to be able to implement the Display
    /// trait, in which case there is no type context available and we print
    /// the ADT ids rather than their names.
    pub fn fmt_with_ctx<'a, 'b, T>(&'a self, ctx: &'b T) -> String
    where
        R: 'a,
        T: Formatter<TypeVarId::Id> + Formatter<TypeDefId::Id> + Formatter<&'a R>,
    {
        match self {
            Ty::Adt(id, regions, inst_types) => {
                let adt_ident = id.fmt_with_ctx(ctx);

                let num_params = regions.len() + inst_types.len();

                let regions: Vec<String> = regions.iter().map(|r| ctx.format_object(r)).collect();
                let mut types: Vec<String> = inst_types
                    .iter()
                    .map(|ty| format!("{}", ty.fmt_with_ctx(ctx)).to_owned())
                    .collect();
                let mut all_params = regions;
                all_params.append(&mut types);
                let all_params = all_params.join(", ");

                if id.is_tuple() {
                    format!("({})", all_params).to_owned()
                } else if num_params > 0 {
                    format!("{}<{}>", adt_ident, all_params).to_owned()
                } else {
                    adt_ident
                }
            }
            Ty::TypeVar(id) => ctx.format_object(*id),
            Ty::Bool => "bool".to_owned(),
            Ty::Char => "char".to_owned(),
            Ty::Never => "!".to_owned(),
            Ty::Integer(int_ty) => format!("{}", integer_ty_to_string(*int_ty)).to_owned(),
            Ty::Str => format!("str").to_owned(),
            Ty::Array(ty) => format!("[{}; ?]", ty.fmt_with_ctx(ctx)).to_owned(),
            Ty::Slice(ty) => format!("[{}]", ty.fmt_with_ctx(ctx)).to_owned(),
            Ty::Ref(r, ty, kind) => match kind {
                RefKind::Mut => {
                    format!("&{} mut ({})", ctx.format_object(r), ty.fmt_with_ctx(ctx)).to_owned()
                }
                RefKind::Shared => {
                    format!("&{} ({})", ctx.format_object(r), ty.fmt_with_ctx(ctx)).to_owned()
                }
            },
        }
    }

    /// Return true if the type is Box
    pub fn is_box(&self) -> bool {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Box), regions, tys) => {
                assert!(regions.is_empty());
                assert!(tys.len() == 1);
                true
            }
            _ => false,
        }
    }

    pub fn as_box(&self) -> Option<&Ty<R>> {
        match self {
            Ty::Adt(TypeId::Assumed(AssumedTy::Box), regions, tys) => {
                assert!(regions.is_empty());
                assert!(tys.len() == 1);
                Some(tys.get(0).unwrap())
            }
            _ => None,
        }
    }
}

impl<Rid: Copy + Eq + Ord + std::hash::Hash> Ty<Region<Rid>> {
    /// Returns `true` if the type contains one of the regions listed
    /// in the set
    pub fn contains_region_var(&self, rset: &OrdSet<Rid>) -> bool {
        match self {
            Ty::TypeVar(_) => false,
            Ty::Bool | Ty::Char | Ty::Never | Ty::Integer(_) | Ty::Str => false,
            Ty::Array(ty) | Ty::Slice(ty) => ty.contains_region_var(rset),
            Ty::Ref(r, _, _) => r.contains_var(rset),
            Ty::Adt(_, regions, tys) => regions
                .iter()
                .any(|r| r.contains_var(rset) || tys.iter().any(|x| x.contains_region_var(rset))),
        }
    }
}

pub fn type_var_id_to_pretty_string(id: TypeVarId::Id) -> String {
    format!("@T{}", id.to_string()).to_owned()
}

impl<Rid: Copy + Eq> std::fmt::Display for Region<Rid>
where
    Rid: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        match self {
            Region::Static => write!(f, "'static"),
            Region::Var(id) => write!(f, "'_{}", id.to_string()),
        }
    }
}

impl std::fmt::Display for ErasedRegion {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::result::Result<(), std::fmt::Error> {
        write!(f, "'_")
    }
}

pub struct DummyFormatter {}

impl Formatter<TypeVarId::Id> for DummyFormatter {
    fn format_object(&self, id: TypeVarId::Id) -> String {
        type_var_id_to_pretty_string(id)
    }
}

impl<Rid: Copy + Eq> Formatter<&Region<Rid>> for DummyFormatter
where
    DummyFormatter: Formatter<Rid>,
{
    fn format_object(&self, r: &Region<Rid>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl Formatter<&ErasedRegion> for DummyFormatter {
    fn format_object(&self, _: &ErasedRegion) -> String {
        "'_".to_string()
    }
}

impl Formatter<RegionVarId::Id> for DummyFormatter {
    fn format_object(&self, id: RegionVarId::Id) -> String {
        region_var_id_to_pretty_string(id)
    }
}

impl Formatter<TypeDefId::Id> for DummyFormatter {
    fn format_object(&self, id: TypeDefId::Id) -> String {
        type_def_id_to_pretty_string(id)
    }
}

impl std::string::ToString for Ty<ErasedRegion> {
    fn to_string(&self) -> String {
        self.fmt_with_ctx(&DummyFormatter {})
    }
}

impl<R> Ty<R>
where
    R: Clone + Eq,
{
    pub fn substitute<R1>(
        &self,
        rsubst: &dyn Fn(&R) -> R1,
        tsubst: &dyn Fn(&TypeVarId::Id) -> Ty<R1>,
    ) -> Ty<R1>
    where
        R1: Clone + Eq,
    {
        match self {
            Ty::Adt(id, regions, tys) => {
                let nregions = Ty::substitute_regions(regions, rsubst);
                let ntys = tys.iter().map(|ty| ty.substitute(rsubst, tsubst)).collect();
                return Ty::Adt(*id, nregions, ntys);
            }
            Ty::TypeVar(id) => {
                return tsubst(id);
            }
            Ty::Bool => Ty::Bool,
            Ty::Char => Ty::Char,
            Ty::Never => Ty::Never,
            Ty::Integer(k) => Ty::Integer(*k),
            Ty::Str => Ty::Str,
            Ty::Array(ty) => {
                return Ty::Array(Box::new(ty.substitute(rsubst, tsubst)));
            }
            Ty::Slice(ty) => {
                return Ty::Slice(Box::new(ty.substitute(rsubst, tsubst)));
            }
            Ty::Ref(rid, ty, kind) => {
                return Ty::Ref(rsubst(rid), Box::new(ty.substitute(rsubst, tsubst)), *kind);
            }
        }
    }

    fn substitute_regions<R1>(regions: &Vector<R>, rsubst: &dyn Fn(&R) -> R1) -> Vector<R1>
    where
        R1: Clone + Eq,
    {
        use std::iter::FromIterator;
        Vector::from_iter(regions.iter().map(|rid| rsubst(rid)))
    }

    /// Substitute the type parameters
    pub fn substitute_types(&self, subst: &TypeSubst<R>) -> Self {
        self.substitute(&|r| r.clone(), &|tid| subst.get(tid).unwrap().clone())
    }

    /// Erase the regions
    pub fn erase_regions(&self) -> ETy {
        self.substitute(&|_| ErasedRegion::Erased, &|tid| Ty::TypeVar(*tid))
    }

    /// Erase the regions and substitute the types at the same time
    pub fn erase_regions_substitute_types(&self, subst: &TypeSubst<ErasedRegion>) -> ETy {
        self.substitute(&|_| ErasedRegion::Erased, &|tid| {
            subst.get(tid).unwrap().clone()
        })
    }

    /// Returns `true` if the type contains some region or type variables
    pub fn contains_variables(&self) -> bool {
        match self {
            Ty::TypeVar(_) => true,
            Ty::Bool | Ty::Char | Ty::Never | Ty::Integer(_) | Ty::Str => false,
            Ty::Array(ty) | Ty::Slice(ty) => ty.contains_variables(),
            Ty::Ref(_, _, _) => true, // Always contains a region identifier
            Ty::Adt(_, regions, tys) => {
                !regions.is_empty() || tys.iter().any(|x| x.contains_variables())
            }
        }
    }

    /// Returns `true` if the type contains some regions
    pub fn contains_regions(&self) -> bool {
        match self {
            Ty::TypeVar(_) => false,
            Ty::Bool | Ty::Char | Ty::Never | Ty::Integer(_) | Ty::Str => false,
            Ty::Array(ty) | Ty::Slice(ty) => ty.contains_regions(),
            Ty::Ref(_, _, _) => true,
            Ty::Adt(_, regions, tys) => {
                !regions.is_empty() || tys.iter().any(|x| x.contains_regions())
            }
        }
    }
}

use std::iter::Iterator;

pub fn make_subst<'a, T1, T2: 'a, I1: Iterator<Item = T1>, I2: Iterator<Item = &'a T2>>(
    keys: I1,
    values: I2,
) -> HashMap<T1, T2>
where
    T1: std::hash::Hash + Eq + Clone + Copy,
    T2: Clone,
{
    // We don't need to do this, but we want to check the lengths
    let keys: Vector<T1> = keys.collect();
    let values: Vector<T2> = values.map(|ty| ty.clone()).collect();
    assert!(
        keys.len() == values.len(),
        "keys and values don't have the same length"
    );

    let mut res: HashMap<T1, T2> = HashMap::new();
    keys.iter().zip(values.into_iter()).for_each(|(p, ty)| {
        let _ = res.insert(*p, ty);
    });

    return res;
}

pub fn make_type_subst<
    'a,
    R: 'a + Eq,
    I1: Iterator<Item = TypeVarId::Id>,
    I2: Iterator<Item = &'a Ty<R>>,
>(
    params: I1,
    types: I2,
) -> TypeSubst<R>
where
    R: Clone,
{
    make_subst(params, types)
}

pub fn make_region_subst<
    'a,
    R: 'a + Eq,
    I1: Iterator<Item = RegionVarId::Id>,
    I2: Iterator<Item = &'a R>,
>(
    keys: I1,
    values: I2,
) -> RegionSubst<R>
where
    R: Clone,
{
    make_subst(keys, values)
}

impl TypeDefs {
    pub fn new() -> TypeDefs {
        TypeDefs {
            types: id_vector::Vector::new(),
        }
    }

    pub fn get_type_def(&self, type_id: TypeDefId::Id) -> Option<&TypeDef> {
        self.types.get(type_id)
    }
}

impl Formatter<TypeDefId::Id> for TypeDefs {
    fn format_object(&self, id: TypeDefId::Id) -> String {
        let def = self.get_type_def(id).unwrap();
        def.name.to_string()
    }
}

impl<R: Clone + std::cmp::Eq + Serialize> Serialize for Ty<R> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "Ty";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        // It seems the "standard" way of doing is the following (this is
        // consistent with what the automatically generated serializer does):
        // - if the arity is > 0, use `serialize_tuple_variant`
        // - otherwise simply serialize a string with the variant name
        if variant_arity > 0 {
            let mut vs = serializer.serialize_tuple_variant(
                enum_name,
                variant_index,
                variant_name,
                variant_arity,
            )?;
            match self {
                Ty::Adt(id, regions, tys) => {
                    vs.serialize_field(id)?;
                    let regions = VectorSerializer::new(regions);
                    vs.serialize_field(&regions)?;
                    let tys = VectorSerializer::new(tys);
                    vs.serialize_field(&tys)?;
                }
                Ty::TypeVar(var_id) => {
                    vs.serialize_field(var_id)?;
                }
                Ty::Bool | Ty::Char | Ty::Never | Ty::Str => {
                    unreachable!();
                }
                Ty::Integer(int_ty) => {
                    vs.serialize_field(int_ty)?;
                }
                Ty::Array(ty) => {
                    vs.serialize_field(ty)?;
                }
                Ty::Slice(ty) => {
                    vs.serialize_field(ty)?;
                }
                Ty::Ref(region, ty, ref_kind) => {
                    vs.serialize_field(region)?;
                    vs.serialize_field(ty)?;
                    vs.serialize_field(ref_kind)?;
                }
            }
            vs.end()
        } else {
            variant_name.serialize(serializer)
        }
    }
}
