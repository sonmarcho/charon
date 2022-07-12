use crate::im_ast as ast;
use crate::llbc_ast as llbc;
use crate::rust_to_local_ids::*;
use std::collections::{HashMap, HashSet};
use std::iter::FromIterator;

fn statement_diverges(divergent: &HashMap<ast::FunDeclId::Id, bool>, st: &llbc::Statement) -> bool {
    match st {
        llbc::Statement::Assign(_, _)
        | llbc::Statement::AssignGlobal(_, _)
        | llbc::Statement::FakeRead(_)
        | llbc::Statement::SetDiscriminant(_, _)
        | llbc::Statement::Drop(_)
        | llbc::Statement::Assert(_)
        | llbc::Statement::Panic
        | llbc::Statement::Return
        | llbc::Statement::Break(_)
        | llbc::Statement::Continue(_)
        | llbc::Statement::Nop => false,
        llbc::Statement::Call(call) => match &call.func {
            ast::FunId::Regular(id) => *divergent.get(id).unwrap(),
            ast::FunId::Assumed(id) => match id {
                ast::AssumedFunId::Replace
                | ast::AssumedFunId::BoxNew
                | ast::AssumedFunId::BoxDeref
                | ast::AssumedFunId::BoxDerefMut
                | ast::AssumedFunId::BoxFree
                | ast::AssumedFunId::VecNew
                | ast::AssumedFunId::VecPush
                | ast::AssumedFunId::VecInsert
                | ast::AssumedFunId::VecLen
                | ast::AssumedFunId::VecIndex
                | ast::AssumedFunId::VecIndexMut => false,
            },
        },
        llbc::Statement::Sequence(st1, st2) => {
            statement_diverges(divergent, &st1) || statement_diverges(divergent, &st2)
        }
        llbc::Statement::Switch(_, tgts) => {
            let tgts = tgts.get_targets();
            tgts.iter().any(|st| statement_diverges(divergent, st))
        }
        llbc::Statement::Loop(_) => true,
    }
}

fn fun_diverges(divergent: &HashMap<ast::FunDeclId::Id, bool>, def: &llbc::FunDecl) -> bool {
    match &def.body {
        Option::Some(body) => statement_diverges(divergent, &body.body),
        Option::None => {
            // Opaque function: we are being a bit conservative here
            true
        }
    }
}

/// Compute which functions can loop.
/// This is a rather crude analysis, which simply checks if a function is
/// recursive or contains a loop, or transitively calls such a function.
/// In the future, we may perform more precise analyses later to check if a
/// recursive function or a function containing a loop is actually structurally
/// terminating.
pub fn compute_divergent_functions(
    decls: &OrderedDecls,
    defs: &llbc::FunDecls,
) -> HashSet<ast::FunDeclId::Id> {
    // For sanity, we use a map rather than a set, so that we can check
    // that we have indeed computed the divergence for the previous
    // declarations.
    let mut divergent_map: HashMap<ast::FunDeclId::Id, bool> = HashMap::new();

    // The declarations in decls have been reordered so that the dependencies
    // of every group of declarations is either in the group itself (in case
    // of recursive functions), in declarations from external crates, or
    // in declarations which happen before in the list of declarations.
    for decl in &decls.decls {
        match decl {
            DeclarationGroup::Fun(GDeclarationGroup::NonRec(id)) => {
                // Non-recursive function: we have to check the body
                divergent_map.insert(*id, fun_diverges(&divergent_map, defs.get(*id).unwrap()));
            }
            DeclarationGroup::Fun(GDeclarationGroup::Rec(ids)) => {
                // Trivial case: recursive declarations can diverge
                for id in ids {
                    divergent_map.insert(*id, true);
                }
            }
            DeclarationGroup::Type(_) | DeclarationGroup::Global(_) => {
                // Ignore the type and global declarations
                continue;
            }
        }
    }

    // Convert the map to a set
    let divergent_set: HashSet<ast::FunDeclId::Id> = HashSet::from_iter(
        divergent_map
            .iter()
            .filter(|(_, div)| **div)
            .map(|(id, _)| *id),
    );
    divergent_set
}
