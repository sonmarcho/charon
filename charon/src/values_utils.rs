//! Implementations for values.rs

#![allow(dead_code)]

use crate::common::*;
use crate::formatter::Formatter;
use crate::im_ast::GlobalDeclId;
use crate::types::*;
use crate::values::*;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};

pub fn var_id_to_pretty_string(id: VarId::Id) -> String {
    format!("var@{}", id.to_string()).to_owned()
}

pub struct DummyFormatter {}

impl Formatter<VarId::Id> for DummyFormatter {
    fn format_object(&self, id: VarId::Id) -> String {
        var_id_to_pretty_string(id)
    }
}

impl Formatter<TypeDeclId::Id> for DummyFormatter {
    fn format_object(&self, id: TypeDeclId::Id) -> String {
        type_def_id_to_pretty_string(id)
    }
}

impl Formatter<GlobalDeclId::Id> for DummyFormatter {
    fn format_object(&self, id: GlobalDeclId::Id) -> String {
        const_def_id_to_pretty_string(id)
    }
}

impl Formatter<(TypeDeclId::Id, VariantId::Id)> for DummyFormatter {
    fn format_object(&self, id: (TypeDeclId::Id, VariantId::Id)) -> String {
        let (def_id, variant_id) = id;
        format!(
            "{}::@Variant{}",
            self.format_object(def_id),
            variant_id.to_string()
        )
        .to_owned()
    }
}

impl Formatter<(TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)> for DummyFormatter {
    fn format_object(&self, id: (TypeDeclId::Id, Option<VariantId::Id>, FieldId::Id)) -> String {
        let (_def_id, _opt_variant_id, field_id) = id;
        format!("@field{}", field_id.to_string()).to_owned()
    }
}

impl ScalarValue {
    pub fn get_integer_ty(&self) -> IntegerTy {
        match self {
            ScalarValue::Isize(_) => IntegerTy::Isize,
            ScalarValue::I8(_) => IntegerTy::I8,
            ScalarValue::I16(_) => IntegerTy::I16,
            ScalarValue::I32(_) => IntegerTy::I32,
            ScalarValue::I64(_) => IntegerTy::I64,
            ScalarValue::I128(_) => IntegerTy::I128,
            ScalarValue::Usize(_) => IntegerTy::Usize,
            ScalarValue::U8(_) => IntegerTy::U8,
            ScalarValue::U16(_) => IntegerTy::U16,
            ScalarValue::U32(_) => IntegerTy::U32,
            ScalarValue::U64(_) => IntegerTy::U64,
            ScalarValue::U128(_) => IntegerTy::U128,
        }
    }

    pub fn is_min(&self) -> bool {
        match self {
            ScalarValue::Isize(v) => *v == isize::MIN,
            ScalarValue::I8(v) => *v == i8::MIN,
            ScalarValue::I16(v) => *v == i16::MIN,
            ScalarValue::I32(v) => *v == i32::MIN,
            ScalarValue::I64(v) => *v == i64::MIN,
            ScalarValue::I128(v) => *v == i128::MIN,
            ScalarValue::Usize(v) => *v == usize::MIN,
            ScalarValue::U8(v) => *v == u8::MIN,
            ScalarValue::U16(v) => *v == u16::MIN,
            ScalarValue::U32(v) => *v == u32::MIN,
            ScalarValue::U64(v) => *v == u64::MIN,
            ScalarValue::U128(v) => *v == u128::MIN,
        }
    }

    pub fn is_int(&self) -> bool {
        match self {
            ScalarValue::Isize(_)
            | ScalarValue::I8(_)
            | ScalarValue::I16(_)
            | ScalarValue::I32(_)
            | ScalarValue::I64(_)
            | ScalarValue::I128(_) => true,
            _ => false,
        }
    }

    pub fn is_uint(&self) -> bool {
        match self {
            ScalarValue::Usize(_)
            | ScalarValue::U8(_)
            | ScalarValue::U16(_)
            | ScalarValue::U32(_)
            | ScalarValue::U64(_)
            | ScalarValue::U128(_) => true,
            _ => false,
        }
    }

    /// When computing the result of binary operations, we convert the values
    /// to u128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_uint(&self) -> Result<u128> {
        match self {
            ScalarValue::Usize(v) => Ok(*v as u128),
            ScalarValue::U8(v) => Ok(*v as u128),
            ScalarValue::U16(v) => Ok(*v as u128),
            ScalarValue::U32(v) => Ok(*v as u128),
            ScalarValue::U64(v) => Ok(*v as u128),
            ScalarValue::U128(v) => Ok(*v),
            _ => Err(()),
        }
    }

    pub fn uint_is_in_bounds(ty: IntegerTy, v: u128) -> bool {
        match ty {
            IntegerTy::Usize => v <= (usize::MAX as u128),
            IntegerTy::U8 => v <= (u8::MAX as u128),
            IntegerTy::U16 => v <= (u16::MAX as u128),
            IntegerTy::U32 => v <= (u32::MAX as u128),
            IntegerTy::U64 => v <= (u64::MAX as u128),
            IntegerTy::U128 => true,
            _ => false,
        }
    }

    pub fn from_unchecked_uint(ty: IntegerTy, v: u128) -> ScalarValue {
        match ty {
            IntegerTy::Usize => ScalarValue::Usize(v as usize),
            IntegerTy::U8 => ScalarValue::U8(v as u8),
            IntegerTy::U16 => ScalarValue::U16(v as u16),
            IntegerTy::U32 => ScalarValue::U32(v as u32),
            IntegerTy::U64 => ScalarValue::U64(v as u64),
            IntegerTy::U128 => ScalarValue::U128(v),
            _ => panic!("Expected an unsigned integer kind"),
        }
    }

    pub fn from_uint(ty: IntegerTy, v: u128) -> Result<ScalarValue> {
        if !ScalarValue::uint_is_in_bounds(ty, v) {
            trace!("Not in bounds for {:?}: {}", ty, v);
            Err(())
        } else {
            Ok(ScalarValue::from_unchecked_uint(ty, v))
        }
    }

    /// When computing the result of binary operations, we convert the values
    /// to i128 then back to the target type (while performing dynamic checks
    /// of course).
    pub fn as_int(&self) -> Result<i128> {
        match self {
            ScalarValue::Isize(v) => Ok(*v as i128),
            ScalarValue::I8(v) => Ok(*v as i128),
            ScalarValue::I16(v) => Ok(*v as i128),
            ScalarValue::I32(v) => Ok(*v as i128),
            ScalarValue::I64(v) => Ok(*v as i128),
            ScalarValue::I128(v) => Ok(*v),
            _ => Err(()),
        }
    }

    pub fn int_is_in_bounds(ty: IntegerTy, v: i128) -> bool {
        match ty {
            IntegerTy::Isize => v >= (isize::MIN as i128) && v <= (isize::MAX as i128),
            IntegerTy::I8 => v >= (i8::MIN as i128) && v <= (i8::MAX as i128),
            IntegerTy::I16 => v >= (i16::MIN as i128) && v <= (i16::MAX as i128),
            IntegerTy::I32 => v >= (i32::MIN as i128) && v <= (i32::MAX as i128),
            IntegerTy::I64 => v >= (i64::MIN as i128) && v <= (i64::MAX as i128),
            IntegerTy::I128 => true,
            _ => false,
        }
    }

    pub fn from_unchecked_int(ty: IntegerTy, v: i128) -> ScalarValue {
        match ty {
            IntegerTy::Isize => ScalarValue::Isize(v as isize),
            IntegerTy::I8 => ScalarValue::I8(v as i8),
            IntegerTy::I16 => ScalarValue::I16(v as i16),
            IntegerTy::I32 => ScalarValue::I32(v as i32),
            IntegerTy::I64 => ScalarValue::I64(v as i64),
            IntegerTy::I128 => ScalarValue::I128(v),
            _ => panic!("Expected a signed integer kind"),
        }
    }

    pub fn from_le_bytes(ty: IntegerTy, b: [u8; 16]) -> ScalarValue {
        use std::convert::TryInto;
        match ty {
            IntegerTy::Isize => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::Isize(isize::from_le_bytes(b))
            }
            IntegerTy::I8 => {
                let b: [u8; 1] = b[0..1].try_into().unwrap();
                ScalarValue::I8(i8::from_le_bytes(b))
            }
            IntegerTy::I16 => {
                let b: [u8; 2] = b[0..2].try_into().unwrap();
                ScalarValue::I16(i16::from_le_bytes(b))
            }
            IntegerTy::I32 => {
                let b: [u8; 4] = b[0..4].try_into().unwrap();
                ScalarValue::I32(i32::from_le_bytes(b))
            }
            IntegerTy::I64 => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::I64(i64::from_le_bytes(b))
            }
            IntegerTy::I128 => {
                let b: [u8; 16] = b[0..16].try_into().unwrap();
                ScalarValue::I128(i128::from_le_bytes(b))
            }
            IntegerTy::Usize => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::Usize(usize::from_le_bytes(b))
            }
            IntegerTy::U8 => {
                let b: [u8; 1] = b[0..1].try_into().unwrap();
                ScalarValue::U8(u8::from_le_bytes(b))
            }
            IntegerTy::U16 => {
                let b: [u8; 2] = b[0..2].try_into().unwrap();
                ScalarValue::U16(u16::from_le_bytes(b))
            }
            IntegerTy::U32 => {
                let b: [u8; 4] = b[0..4].try_into().unwrap();
                ScalarValue::U32(u32::from_le_bytes(b))
            }
            IntegerTy::U64 => {
                let b: [u8; 8] = b[0..8].try_into().unwrap();
                ScalarValue::U64(u64::from_le_bytes(b))
            }
            IntegerTy::U128 => {
                let b: [u8; 16] = b[0..16].try_into().unwrap();
                ScalarValue::U128(u128::from_le_bytes(b))
            }
        }
    }

    /// **Warning**: most constants are stored as u128 by rustc. When converting
    /// to i128, it is not correct to do `v as i128`, we must reinterpret the
    /// bits (see [from_le_bytes]).
    pub fn from_int(ty: IntegerTy, v: i128) -> Result<ScalarValue> {
        if !ScalarValue::int_is_in_bounds(ty, v) {
            Err(())
        } else {
            Ok(ScalarValue::from_unchecked_int(ty, v))
        }
    }
}

impl std::string::ToString for ScalarValue {
    fn to_string(&self) -> String {
        match self {
            ScalarValue::Isize(v) => format!("{} : isize", v).to_owned(),
            ScalarValue::I8(v) => format!("{} : i8", v).to_owned(),
            ScalarValue::I16(v) => format!("{} : i16", v).to_owned(),
            ScalarValue::I32(v) => format!("{} : i32", v).to_owned(),
            ScalarValue::I64(v) => format!("{} : i64", v).to_owned(),
            ScalarValue::I128(v) => format!("{} : i128", v).to_owned(),
            ScalarValue::Usize(v) => format!("{} : usize", v).to_owned(),
            ScalarValue::U8(v) => format!("{} : u8", v).to_owned(),
            ScalarValue::U16(v) => format!("{} : u16", v).to_owned(),
            ScalarValue::U32(v) => format!("{} : u32", v).to_owned(),
            ScalarValue::U64(v) => format!("{} : u64", v).to_owned(),
            ScalarValue::U128(v) => format!("{} : u128", v).to_owned(),
        }
    }
}

impl std::string::ToString for ConstantValue {
    fn to_string(&self) -> String {
        match self {
            ConstantValue::Scalar(v) => v.to_string(),
            ConstantValue::Bool(v) => v.to_string(),
            ConstantValue::Char(v) => v.to_string(),
            ConstantValue::String(v) => v.to_string(),
        }
    }
}

impl Serialize for ScalarValue {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "ScalarValue";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        if variant_arity > 0 {
            let mut vs = serializer.serialize_tuple_variant(
                enum_name,
                variant_index,
                variant_name,
                variant_arity,
            )?;
            match self {
                ScalarValue::Isize(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::I8(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::I16(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::I32(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::I64(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::I128(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::Usize(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::U8(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::U16(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::U32(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::U64(i) => vs.serialize_field(&i.to_string())?,
                ScalarValue::U128(i) => vs.serialize_field(&i.to_string())?,
            };
            vs.end()
        } else {
            variant_name.serialize(serializer)
        }
    }
}
