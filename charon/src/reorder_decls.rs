use crate::common::*;
use crate::graphs::*;
use crate::register::DeclKind;
use crate::register::RegisteredDeclarations;
use macros::EnumAsGetters;
use macros::EnumIsA;
use macros::{VariantIndexArity, VariantName};
use petgraph::algo::tarjan_scc;
use petgraph::graphmap::DiGraphMap;
use rustc_hir::def_id::DefId;
use serde::ser::SerializeTupleVariant;
use serde::{Serialize, Serializer};
use std::collections::HashMap;
use std::fmt::{Debug, Display, Error, Formatter};
use std::vec::Vec;

/// A (group of) top-level declaration(s), properly reordered.
/// "G" stands for "generic"
#[derive(Debug, VariantIndexArity, VariantName)]
pub enum GDeclarationGroup<Id: Copy> {
    /// A non-recursive declaration
    NonRec(Id),
    /// A (group of mutually) recursive declaration(s)
    Rec(Vec<Id>),
}

/// A (group of) top-level declaration(s), properly reordered.
#[derive(Debug, VariantIndexArity, VariantName)]
pub enum DeclarationGroup<TypeId: Copy, FunId: Copy, GlobalId: Copy> {
    /// A type declaration group
    Type(GDeclarationGroup<TypeId>),
    /// A function declaration group
    Fun(GDeclarationGroup<FunId>),
    /// A global declaration group
    Global(GDeclarationGroup<GlobalId>),
}

#[derive(PartialEq, Eq, Hash, EnumIsA, EnumAsGetters, VariantName)]
pub enum AnyDeclId<TypeId: Copy, FunId: Copy, GlobalId: Copy> {
    Type(TypeId),
    Fun(FunId),
    Global(GlobalId),
}

#[derive(Clone, Copy)]
pub struct DeclInfo {
    pub is_transparent: bool,
}

/// The top-level declarations in a module and their external dependencies.
/// External declarations are recognizable with `DefId::is_local()`:
/// See [rust_to_local_ids.rs].
pub struct DeclarationsGroups<TypeId: Copy, FunId: Copy, GlobalId: Copy> {
    /// The properly grouped and ordered declarations
    pub decls: Vec<DeclarationGroup<TypeId, FunId, GlobalId>>,
    /// All the type ids
    pub type_ids: Vec<TypeId>,
    /// All the function ids
    pub fun_ids: Vec<FunId>,
    /// All the global ids
    pub global_ids: Vec<GlobalId>,
    /// Additional information on declarations
    pub decls_info: HashMap<AnyDeclId<TypeId, FunId, GlobalId>, DeclInfo>,
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<Id: Copy + Debug> Display for GDeclarationGroup<Id> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            GDeclarationGroup::NonRec(id) => write!(f, "non-rec: {:?}", id),
            GDeclarationGroup::Rec(ids) => write!(
                f,
                "rec: {}",
                vec_to_string(&|id| format!("    {:?}", id).to_string(), ids)
            ),
        }
    }
}

/// This is a bit annoying: because [DefId] and [Vec] doe't implement the
/// [Serialize] trait, we can't automatically derive the serializing trait...
impl<Id: Copy + Serialize> Serialize for GDeclarationGroup<Id> {
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "GDeclarationGroup";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        assert!(variant_arity > 0);
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            GDeclarationGroup::NonRec(id) => {
                vs.serialize_field(id)?;
            }
            GDeclarationGroup::Rec(ids) => {
                let ids = VecSerializer::new(ids);
                vs.serialize_field(&ids)?;
            }
        }
        vs.end()
    }
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<TypeId: Copy + Debug, FunId: Copy + Debug, GlobalId: Copy + Debug> Display
    for DeclarationGroup<TypeId, FunId, GlobalId>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        match self {
            DeclarationGroup::Type(decl) => write!(f, "{{ Type(s): {} }}", decl),
            DeclarationGroup::Fun(decl) => write!(f, "{{ Fun(s): {} }}", decl),
            DeclarationGroup::Global(decl) => write!(f, "{{ Global(s): {} }}", decl),
        }
    }
}

/// This is a bit annoying: because [DefId] and [Vec] doe't implement the
/// [Serialize] trait, we can't automatically derive the serializing trait...
impl<TypeId: Copy + Serialize, FunId: Copy + Serialize, GlobalId: Copy + Serialize> Serialize
    for DeclarationGroup<TypeId, FunId, GlobalId>
{
    fn serialize<S>(&self, serializer: S) -> std::result::Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let enum_name = "DeclarationGroup";
        let variant_name = self.variant_name();
        let (variant_index, variant_arity) = self.variant_index_arity();
        assert!(variant_arity > 0);
        let mut vs = serializer.serialize_tuple_variant(
            enum_name,
            variant_index,
            variant_name,
            variant_arity,
        )?;
        match self {
            DeclarationGroup::Type(decl) => {
                vs.serialize_field(decl)?;
            }
            DeclarationGroup::Fun(decl) => {
                vs.serialize_field(decl)?;
            }
            DeclarationGroup::Global(decl) => {
                vs.serialize_field(decl)?;
            }
        }
        vs.end()
    }
}

impl<TypeId: Copy, FunId: Copy, GlobalId: Copy> DeclarationsGroups<TypeId, FunId, GlobalId> {
    pub fn new() -> DeclarationsGroups<TypeId, FunId, GlobalId> {
        DeclarationsGroups {
            decls: vec![],
            type_ids: vec![],
            fun_ids: vec![],
            global_ids: vec![],
            decls_info: HashMap::new(),
        }
    }

    fn push(&mut self, decl: DeclarationGroup<TypeId, FunId, GlobalId>) {
        match &decl {
            DeclarationGroup::Type(GDeclarationGroup::NonRec(id)) => {
                self.type_ids.push(*id);
            }
            DeclarationGroup::Type(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.type_ids.push(*id);
                }
            }
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)) => {
                self.fun_ids.push(*id);
            }
            DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.fun_ids.push(*id);
                }
            }
            DeclarationGroup::Global(GDeclarationGroup::NonRec(id)) => {
                self.global_ids.push(*id);
            }
            DeclarationGroup::Global(GDeclarationGroup::Rec(ids)) => {
                for id in ids {
                    self.global_ids.push(*id);
                }
            }
        }
        self.decls.push(decl);
    }
}

/// We use the [Debug] trait instead of [Display] for the identifiers, because
/// the rustc [DefId] doesn't implement [Display]...
impl<TypeId: Copy + Debug, FunId: Copy + Debug, GlobalId: Copy + Debug> Display
    for DeclarationsGroups<TypeId, FunId, GlobalId>
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::result::Result<(), Error> {
        write!(
            f,
            "{}",
            vec_to_string(
                &|d: &DeclarationGroup<TypeId, FunId, GlobalId>| d.to_string(),
                &self.decls,
            )
        )
    }
}

impl<'a, TypeId: Copy, FunId: Copy, GlobalId: Copy> std::iter::IntoIterator
    for &'a DeclarationsGroups<TypeId, FunId, GlobalId>
{
    type Item = &'a DeclarationGroup<TypeId, FunId, GlobalId>;
    type IntoIter = std::slice::Iter<'a, DeclarationGroup<TypeId, FunId, GlobalId>>;

    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.decls.iter()
    }
}

pub fn reorder_declarations(
    decls: &RegisteredDeclarations,
) -> Result<DeclarationsGroups<DefId, DefId, DefId>> {
    trace!();

    // Step 1: Start by building the graph
    let mut graph = DiGraphMap::<DefId, ()>::new();

    // Add the nodes - note that we are using both local and external def ids.
    for (id, _) in decls.iter() {
        graph.add_node(*id);
    }

    // Add the edges, which go from a declaration to its dependency.
    for (src, d) in decls.iter() {
        for tgt in d.deps.iter().flatten() {
            graph.add_edge(*src, *tgt, ());
        }
    }

    trace!("Graph: {:?}", graph);

    // Step 2: Apply Tarjan's SCC (Strongly Connected Components) algorithm
    let sccs = tarjan_scc(&graph);

    // Step 3: Reorder the declarations in an order as close as possible to the one
    // given by the user. To be more precise, if we don't need to move
    // definitions, the order in which we generate the declarations should
    // be the same as the one in which the user wrote them.
    let get_id_dependencies = &|id| decls[&id].deps.iter().flatten().map(|d| *d).collect();
    let SCCs {
        sccs: reordered_sccs,
        scc_deps: _,
    } = reorder_sccs::<DefId>(
        get_id_dependencies,
        &decls.iter().map(|(id, _)| *id).collect(),
        &sccs,
    );

    // Finally, generate the list of declarations
    let mut reordered_decls = DeclarationsGroups::new();

    // Iterate over the SCC ids in the proper order
    for scc in reordered_sccs.iter() {
        // Retrieve the SCC
        assert!(scc.len() > 0);

        // Note that the length of an SCC should be at least 1.
        let mut it = scc.iter();
        let id0 = *it.next().unwrap();
        let decl = &decls[&id0];

        // The group should consist of only functions, only types or only one global.
        for id in scc {
            assert!(decls[id].kind == decl.kind);
        }
        if let DeclKind::Global = decl.kind {
            assert!(scc.len() == 1);
        }

        // If an SCC has length one, the declaration may be simply recursive:
        // we determine whether it is the case by checking if the def id is in
        // its own set of dependencies.
        let is_mutually_recursive = scc.len() > 1;
        let is_simply_recursive =
            !is_mutually_recursive && decl.deps.as_ref().is_some_with(|deps| deps.contains(&id0));

        // Add the declaration.
        // Note that we clone the vectors: it is not optimal, but they should
        // be pretty small.
        let group = if is_mutually_recursive || is_simply_recursive {
            GDeclarationGroup::Rec(scc.clone())
        } else {
            GDeclarationGroup::NonRec(id0)
        };
        reordered_decls.push(match decl.kind {
            DeclKind::Type => DeclarationGroup::Type(group),
            DeclKind::Fun => DeclarationGroup::Fun(group),
            DeclKind::Global => DeclarationGroup::Global(group),
        });
    }

    trace!("{}", reordered_decls.to_string());

    // Adds declarations information.
    reordered_decls.decls_info = decls
        .iter()
        .map(|(id, decl)| {
            (
                match decl.kind {
                    DeclKind::Type => AnyDeclId::Type(*id),
                    DeclKind::Fun => AnyDeclId::Fun(*id),
                    DeclKind::Global => AnyDeclId::Global(*id),
                },
                DeclInfo {
                    is_transparent: decl.is_transparent(),
                },
            )
        })
        .collect();

    // TODO: check that the mutually recursive groups don't mix opaque and
    // transparent definitions (this is for sanity: this really *shouldn't*
    // happen).

    return Ok(reordered_decls);
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_reorder_sccs1() {
        let sccs = vec![vec![0], vec![1, 2], vec![3, 4, 5]];
        let ids = vec![0, 1, 2, 3, 4, 5];

        let get_deps = &|x| match x {
            0 => vec![3],
            1 => vec![0, 3],
            _ => vec![],
        };
        let reordered = crate::reorder_decls::reorder_sccs(get_deps, &ids, &sccs);

        assert!(reordered.sccs == vec![vec![3, 4, 5], vec![0], vec![1, 2],]);
        assert!(reordered.scc_deps[0] == im::OrdSet::from(vec![]));
        assert!(reordered.scc_deps[1] == im::OrdSet::from(vec![0]));
        assert!(reordered.scc_deps[2] == im::OrdSet::from(vec![0, 1]));
    }
}
