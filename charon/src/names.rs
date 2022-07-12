//! Defines some utilities for the variables
#![allow(dead_code)]

pub use crate::names_utils::*;
use macros::generate_index_type;
use macros::EnumIsA;
use serde::Serialize;

generate_index_type!(Disambiguator);

/// See the comments for [Name]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, EnumIsA)]
pub enum PathElem {
    Ident(String),
    Disambiguator(Disambiguator::Id),
}

/// An item name/path
///
/// A name really is a list of strings. However, we sometimes need to
/// introduce unique indices to disambiguate. This mostly happens because
/// of "impl" blocks:
///   ```
///   impl<T> List<T> {
///     ...
///   }
///   ```
///
/// A type in Rust can have several "impl" blocks, and  those blocks can
/// contain items with similar names. For this reason, we need to disambiguate
/// them with unique indices. Rustc calls those "disambiguators". In rustc, this
/// gives names like this:
/// - `betree_main::betree::NodeIdCounter{impl#0}::new`
/// - note that impl blocks can be nested, and macros sometimes generate
///   weird names (which require disambiguation):
///   `betree_main::betree_utils::_#1::{impl#0}::deserialize::{impl#0}`
///
/// Finally, the paths used by rustc are a lot more precise and explicit than
/// those we expose in LLBC: for instance, every identifier belongs to a specific
/// namespace (value namespace, type namespace, etc.), and is coupled with a
/// disambiguator.
///
/// On our side, we want to stay high-level and simple: we use string identifiers
/// as much as possible, insert disambiguators only when necessary (whenever
/// we find an "impl" block, typically) and check that the disambiguator is useless
/// in the other situations (i.e., the disambiguator is always equal to 0).
///
/// Moreover, the items are uniquely disambiguated by their (integer) ids
/// (`TypeDeclId::Id`, etc.), and when extracting the code we have to deal with
/// name clashes anyway. Still, we might want to be more precise in the future.
///
/// Also note that the first path element in the name is always the crate name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Name {
    pub name: Vec<PathElem>,
}

pub type ModuleName = Name;
pub type TypeName = Name;
pub type ItemName = Name;
pub type FunName = Name;
pub type GlobalName = Name;
pub type HirItemName = Name;
