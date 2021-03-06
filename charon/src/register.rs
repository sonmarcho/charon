use crate::assumed;
use crate::common::*;
use crate::generics;
use crate::names::{
    function_def_id_to_name, hir_item_to_name, module_def_id_to_name, type_def_id_to_name, FunName,
    TypeName,
};
use crate::translate_functions_to_im;
use hashlink::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use rustc_hir::{
    def_id::DefId, def_id::LocalDefId, Defaultness, ImplItem, ImplItemKind, Item, ItemKind,
};
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::Span;
use std::collections::HashSet;

fn is_fn_decl(item: &Item) -> bool {
    match item.kind {
        ItemKind::Fn(_, _, _) => true,
        _ => false,
    }
}

pub struct CrateInfo {
    pub crate_name: String,
    /// The set of opaque modules
    pub opaque: HashSet<String>,
}

pub type TypeDependencies = LinkedHashSet<DefId>;
pub type FunDependencies = LinkedHashSet<DefId>;

/// A registered type declaration.
/// Simply contains the item id and its dependencies.
#[derive(Debug)]
pub struct RegisteredTypeDeclaration {
    pub type_id: DefId,
    /// The set of type dependencies. It can contain local def ids as well as
    /// external def ids.
    pub deps: TypeDependencies,
}

impl RegisteredTypeDeclaration {
    pub fn new(id: DefId) -> RegisteredTypeDeclaration {
        return RegisteredTypeDeclaration {
            type_id: id,
            deps: LinkedHashSet::new(),
        };
    }
}

/// A registered function declaration.
/// Simply contains the item id and its dependencies.
#[derive(Debug)]
pub struct RegisteredFunDeclaration {
    pub fun_id: DefId,
    /// The set of type dependencies. It can contain local def ids as well as
    /// external def ids.
    pub deps_tys: TypeDependencies,
    /// The tset of function dependencies. It can contain local def ids as well as
    /// external def ids.
    pub deps_funs: FunDependencies,
}

impl RegisteredFunDeclaration {
    pub fn new(id: DefId) -> RegisteredFunDeclaration {
        return RegisteredFunDeclaration {
            fun_id: id,
            deps_tys: LinkedHashSet::new(),
            deps_funs: LinkedHashSet::new(),
        };
    }
}

/// Contains the declarations registered in the first pass of the translation.
/// This pass is used to build the local dependency graph between the declarations,
/// in order to know in which order to translate them, and detect the cycles
/// (i.e.: the mutually recursive definitions).
#[derive(Debug)]
pub struct RegisteredDeclarations {
    /// All the def ids of the declarations to be translated, in the order in
    /// which we registered them. This set can only contain local def ids.
    pub decls: LinkedHashSet<DefId>,

    /// All the type declarations to be translated, and their local
    /// dependencies.
    pub types: LinkedHashMap<DefId, RegisteredTypeDeclaration>,

    /// All the opaque type declarations (local types, but found in modules
    /// that were marked as opaque). Does not include the non-local types.
    pub opaque_types: HashSet<DefId>,

    /// All the function declarations to be translated, and their local
    /// depedencies.
    pub funs: LinkedHashMap<DefId, RegisteredFunDeclaration>,

    /// All the opaque function declarations (local function, but found in modules
    /// that were marked as opaque). Does not include the non-local functions.
    pub opaque_funs: HashSet<DefId>,
}

impl RegisteredDeclarations {
    pub fn new() -> RegisteredDeclarations {
        return RegisteredDeclarations {
            decls: LinkedHashSet::new(),
            types: LinkedHashMap::new(),
            opaque_types: HashSet::new(),
            funs: LinkedHashMap::new(),
            opaque_funs: HashSet::new(),
        };
    }
}

/// Register a HIR type.
/// This function is called when processing top-level declarations. It mostly
/// delegates the work to functions operating on the MIR (and once in MIR we
/// stay in MIR).
/// The caller must have checked if the def_id has been registered before, and
/// must call this function only if it was not the case, and after having added
/// the def_id to the list of registered ids.
fn register_hir_type(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    item: &Item,
    def_id: DefId,
) -> Result<()> {
    trace!();

    match &item.kind {
        ItemKind::TyAlias(_, _) => {
            // It seems type alias are not converted to MIR, and are inlined,
            // so we don't need to do anything. Note that we actually filter
            // type aliases before calling this function.
            trace!("enum");
            unreachable!();
        }
        ItemKind::Struct(_, _) | ItemKind::Enum(_, _) => {
            trace!("adt");

            // Retrieve the MIR adt from the def id and register it, retrieve
            // the list of dependencies at the same time.
            let adt = tcx.adt_def(def_id);
            return register_local_adt(crate_info, rdecls, sess, tcx, adt);
        }
        _ => {
            unreachable!();
        }
    }
}

/// Register a MIR ADT.
/// Note that the def id of the ADT should already have been stored in the set of
/// explored def ids.
fn register_local_adt(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    adt: &AdtDef,
) -> Result<()> {
    trace!("> adt: {:?}", adt);

    // First, retrieve the HIR definition - this function may have been
    // called from MIR code, which is why we don't take an item or a HIR
    // definition as parameter. We use it only for the span, to report
    // precise error messages to the user.
    let hir_map = tcx.hir();
    let item = if let rustc_hir::Node::Item(item) = hir_map.get_if_local(adt.did).unwrap() {
        item
    } else {
        unreachable!();
    };

    // Check the generics - TODO: we check this here and in translate_types
    generics::check_type_generics(tcx, adt.did);

    let type_id = adt.did;

    // Initialize the type declaration that we will register (in particular,
    // initialize the list of local dependencies to empty).
    let mut rtype_decl = RegisteredTypeDeclaration::new(type_id);

    // We explore the type definition only if it is not in a module flagged
    // as opaque
    let name = type_def_id_to_name(tcx, adt.did);
    if name.is_in_modules(&crate_info.crate_name, &crate_info.opaque) {
        // The type is opaque
        // Register it as having no dependencies (dependencise are introduced
        // by exploring the type definition, to check the types used in the fields).
        rdecls.types.insert(type_id, rtype_decl);
        rdecls.opaque_types.insert(type_id);
        return Ok(());
    } else {
        // The type is not opaque

        // Use a dummy substitution to instantiate the type parameters
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(tcx, adt.did);

        // Explore all the variants. Note that we also explore the HIR to retrieve
        // precise spans: for instance, to indicate which variant is problematic
        // in case of an enum.
        let hir_variants: &[rustc_hir::Variant] = match &item.kind {
            ItemKind::Enum(enum_def, _) => enum_def.variants,
            ItemKind::Struct(_, _) => {
                // Nothing to return
                &[]
            }
            _ => {
                unreachable!()
            }
        };

        let mut i = 0; // The index of the variant
        for var_def in adt.variants.iter() {
            trace!("var_def");
            // Retrieve the most precise span (the span of the variant if this is an
            // enum, the span of the whole ADT otherwise).
            let var_span = if adt.is_enum() {
                &hir_variants[i].span
            } else {
                &item.span
            };

            for field_def in var_def.fields.iter() {
                trace!("field_def");
                let ty = field_def.ty(tcx, substs);
                trace!("ty");
                register_mir_ty(
                    crate_info,
                    rdecls,
                    sess,
                    tcx,
                    var_span,
                    &mut rtype_decl.deps,
                    &ty,
                )?;
            }

            i += 1;
        }

        // Add the type declaration to the registered declarations
        rdecls.types.insert(rtype_decl.type_id, rtype_decl);
        return Ok(());
    }
}

/// Register a a non-local MIR ADT.
/// Note that the def id of the ADT should already have been stored in the set of
/// explored def ids.
///
/// For now, we don't do much.
/// In the future, we will explore the ADT, to reveal its public information
/// (public fields in case of a structure, variants in case of a public
/// enumeration).
fn register_non_local_adt(
    _crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    _sess: &Session,
    tcx: TyCtxt,
    adt: &AdtDef,
    name: TypeName,
) -> Result<()> {
    trace!("> non-local adt: {:?}", adt);

    // First, check if the ADT has primitive support: if it is the case, there
    // is nothing to do
    if assumed::type_to_used_params(&name).is_some() {
        // Primitive
        return Ok(());
    }

    // Non-primitive (i.e.: external)
    let type_id = adt.did;

    // Check if registered
    if rdecls.decls.contains(&type_id) {
        return Ok(());
    }
    rdecls.decls.insert(type_id);

    // Check the generics - TODO: we check this here and in translate_types
    generics::check_type_generics(tcx, type_id);

    // Register the type as having no dependencies
    let rtype_decl = RegisteredTypeDeclaration::new(type_id);
    rdecls.types.insert(type_id, rtype_decl);
    rdecls.opaque_types.insert(type_id);

    return Ok(());
}

/// Auxiliary function to register a list of type parameters.
fn register_mir_substs<'tcx>(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    span: &Span,
    deps: &mut TypeDependencies,
    used_params: Option<Vec<bool>>,
    substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<()> {
    trace!("substs: {:?}", substs);

    // Filter the arguments, if necessary
    let params: Vec<rustc_middle::ty::subst::GenericArg<'tcx>> = match used_params {
        Option::None => substs.iter().collect(),
        Option::Some(used_params) => {
            // Note that the substs doesn't necessarily define a substitution
            // for all the parameters, because some of them have default
            // values: for this reason we can't check the length and used the
            // fact that `zip` below stops once one of the two iterators is
            // consumed.
            assert!(substs.len() == used_params.len());
            substs
                .iter()
                .zip(used_params.into_iter())
                .filter_map(|(param, used)| if used { Some(param) } else { None })
                .collect()
        }
    };

    // Register the arguments
    for param in params.into_iter() {
        match param.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, &param_ty)?;
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(_)
            | rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                // Nothing to do
            }
        }
    }
    return Ok(());
}

/// Explore a base type and register all the types inside.
/// There is no need to perform any check on the type (to prevent cyclic calls)
/// before calling this function.
fn register_mir_ty(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    span: &Span,
    deps: &mut TypeDependencies,
    ty: &Ty,
) -> Result<()> {
    trace!("> ty: {:?}", ty);

    match ty.kind() {
        TyKind::Bool
        | TyKind::Char
        | TyKind::Int(_)
        | TyKind::Uint(_)
        | TyKind::Str
        | TyKind::Float(_)
        | TyKind::Never => {
            // Nothing to do
            trace!("base type (Bool, Char, Int...)");
            return Ok(());
        }

        TyKind::Adt(adt, substs) => {
            trace!("Adt");

            // Identify the type by retrieving its name
            let name = type_def_id_to_name(tcx, adt.did);

            // Check if the type is primitive

            // Check if the type is primitive.
            //
            // Note that if the type is primitive, we might ignore
            // some of its parameters (for instance, we ignore the Allocator
            // parameter of `Box` and `Vec`).
            //
            // [used_params] below is an option:
            // - `Some` if the type is primitive and we need to filter some
            //   of its parameters
            // - `None` if it is not primitive (no filter information)
            let used_params = if adt.did.is_local() {
                // We probably do not need to check if the type is local...
                Option::None
            } else {
                assumed::type_to_used_params(&name)
            };

            // We probably don't need to check if the type is local...
            let is_prim = !adt.did.is_local() && used_params.is_some();
            // Add this ADT to the list of dependencies, only if it is not
            // primitive
            if !is_prim {
                deps.insert(adt.did);
            }

            // From now onwards, we do something different depending on
            // whether the type is a local type (i.e., defined in the current
            // crate) or an assumed (external) type like box or vec
            if !adt.did.is_local() {
                // Explore the type parameters instantiation
                // There are two possibilities:
                // - either the type is considered primitive (i.e., it belongs
                //   to a well-identified list of types like `Box` which benefit
                //   from primitive treatment)
                // - or the type is external, in which case we register it as such

                // Explore the type parameters instantiation
                register_mir_substs(
                    crate_info,
                    rdecls,
                    sess,
                    tcx,
                    span,
                    deps,
                    used_params,
                    substs,
                )?;

                // Register the ADT.
                // Note that [register_non_local_adt] checks if the def id
                // has already been registered, and inserts it in the list
                // of def ids if necessary (not the same behaviour as the
                // "local" case, where we do that *before*).
                // TODO: we may want to do this more consistent.
                return register_non_local_adt(crate_info, rdecls, sess, tcx, adt, name);
            } else {
                // Explore the type parameters instantiation
                register_mir_substs(
                    crate_info,
                    rdecls,
                    sess,
                    tcx,
                    span,
                    deps,
                    Option::None,
                    substs,
                )?;

                // Explore the ADT, if we haven't already registered it
                // Check if registered
                if rdecls.decls.contains(&adt.did) {
                    trace!("Adt already registered");
                    return Ok(());
                }
                trace!("Adt not registered");
                rdecls.decls.insert(adt.did);

                // Register and explore
                return register_local_adt(crate_info, rdecls, sess, tcx, adt);
            }
        }
        TyKind::Array(ty, const_param) => {
            trace!("Array");

            register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, ty)?;
            return register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, &const_param.ty);
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            return register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, ty);
        }
        TyKind::Ref(_, ty, _) => {
            trace!("Ref");

            return register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, ty);
        }
        TyKind::Tuple(substs) => {
            trace!("Tuple");

            for param in substs.iter() {
                let param_ty = param.expect_ty();
                register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, &param_ty)?;
            }

            return Ok(());
        }

        TyKind::RawPtr(_) => {
            // A raw pointer
            trace!("RawPtr");
            span_err(sess, span.clone(), "raw pointers are not supported");
            return Err(());
        }
        TyKind::Foreign(_) => {
            // A raw pointer
            trace!("Foreign");
            span_err(sess, span.clone(), "FFI types are not supported");
            return Err(());
        }
        TyKind::Infer(_) => {
            trace!("Infer");
            span_err(
                sess,
                span.clone(),
                "Inconsistant state: found an `Infer` type",
            );
            return Err(());
        }

        TyKind::FnDef(_, _) => {
            // We shouldn't get there
            trace!("FnDef");
            unreachable!();
        }

        TyKind::FnPtr(sig) => {
            trace!("FnPtr");
            for param_ty in sig.inputs_and_output().no_bound_vars().unwrap().iter() {
                register_mir_ty(crate_info, rdecls, sess, tcx, span, deps, &param_ty)?;
            }
            return Ok(());
        }

        TyKind::Dynamic(_, _) => {
            // A trait object
            trace!("Dynamic");
            unimplemented!();
        }
        TyKind::Closure(_, _) => {
            trace!("Closure");
            unimplemented!();
        }

        TyKind::Generator(_, _, _) | TyKind::GeneratorWitness(_) => {
            trace!("Generator");
            span_err(sess, span.clone(), "Generators are not supported");
            return Err(());
        }

        TyKind::Error(_) => {
            trace!("Error");
            span_err(
                sess,
                span.clone(),
                "Error type found: the code doesn't typecheck",
            );
            return Err(());
        }
        TyKind::Projection(_) => {
            unimplemented!();
        }
        TyKind::Opaque(_, _) => {
            unimplemented!();
        }
        TyKind::Param(_) => {
            // A type parameter, for example `T` in `fn f<T>(x : T) {}`
            // We have nothing to do
            trace!("Param");
            return Ok(());
        }
        TyKind::Bound(_, _) => {
            unimplemented!();
        }
        TyKind::Placeholder(_) => {
            unimplemented!();
        }
    }
}

// Extract function information from an operand
fn get_fun_from_operand<'tcx>(
    op: &rustc_middle::mir::Operand<'tcx>,
) -> Option<(DefId, rustc_middle::ty::subst::SubstsRef<'tcx>)> {
    let fun_ty = op.constant().unwrap().literal.ty();
    match fun_ty.kind() {
        TyKind::FnDef(def_id, substs) => return Some((*def_id, substs)),
        _ => {
            return None;
        }
    }
}

/// Rk.: contrary to the "local" case, [register_non_local_function] inserts
/// itself the def id in the declarations list. The reason is that we need
/// to check if the function has primitive support first.
fn register_non_local_function(
    _crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    _sess: &Session,
    tcx: TyCtxt,
    def_id: DefId,
    name: FunName,
) -> Result<()> {
    // First, check if the function has primitive support: if it is the case,
    // there is nothing to do
    if assumed::function_to_info(&name).is_some() {
        // Primitive
        return Ok(());
    }

    // Check if registered
    if rdecls.decls.contains(&def_id) {
        return Ok(());
    }
    rdecls.decls.insert(def_id);

    // Check the generics - TODO: we check this here and in translate_functions_to_im
    generics::check_function_generics(tcx, def_id);

    // Register the function as having no dependencies
    let decl = RegisteredFunDeclaration::new(def_id);
    rdecls.funs.insert(def_id, decl);
    rdecls.opaque_funs.insert(def_id);

    return Ok(());
}

/// Register the identifiers found in a function body
fn register_local_function_body(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    def_id: LocalDefId,
    fn_decl: &mut RegisteredFunDeclaration,
) -> Result<()> {
    // Retrieve the MIR code
    let body = crate::get_mir::get_mir_for_def_id(tcx, def_id);

    // Start by registering the types found in the local variable declarations.
    // Note that those local variables include the parameters as well as the
    // return variable, and is thus enough to register the function signature.
    for v in body.local_decls.iter() {
        register_mir_ty(
            crate_info,
            rdecls,
            sess,
            tcx,
            &v.source_info.span,
            &mut fn_decl.deps_tys,
            &v.ty,
        )?;
    }

    // Explore the body itself.
    // We need it to compute the dependencies between the functions and global
    // declarations, and also because some functions might be parameterized
    // with types which don't appear in the local variables (unlikely, but
    // can happen if some type parameters are not used).
    // We initially considered using visitors, but the MIR visitors return unit,
    // while we need to use a result type...
    // A basic block is a list of statements, followed by a terminator.
    for block in body.basic_blocks().iter() {
        // Statements
        for statement in block.statements.iter() {
            match &statement.kind {
                rustc_middle::mir::StatementKind::Assign(_)
                | rustc_middle::mir::StatementKind::FakeRead(_)
                | rustc_middle::mir::StatementKind::SetDiscriminant {
                    place: _,
                    variant_index: _,
                }
                | rustc_middle::mir::StatementKind::StorageLive(_)
                | rustc_middle::mir::StatementKind::StorageDead(_)
                | rustc_middle::mir::StatementKind::AscribeUserType(_, _)
                | rustc_middle::mir::StatementKind::Coverage(_)
                | rustc_middle::mir::StatementKind::Nop => {
                    // Nothing to do
                }

                rustc_middle::mir::StatementKind::CopyNonOverlapping(_) => {
                    trace!("Copy non overlapping");
                    span_err(
                        sess,
                        statement.source_info.span.clone(),
                        "Copy non overlapping not supported",
                    );
                }
                rustc_middle::mir::StatementKind::Retag(_, _) => {
                    // retag statements are only used by MIRI, so we have nothing
                    // to do
                }
            }
        }

        // Terminator
        let terminator = block.terminator();
        match &terminator.kind {
            rustc_middle::mir::terminator::TerminatorKind::Goto { target: _ }
            | rustc_middle::mir::terminator::TerminatorKind::SwitchInt {
                discr: _,
                switch_ty: _,
                targets: _,
            }
            | rustc_middle::mir::terminator::TerminatorKind::Resume
            | rustc_middle::mir::terminator::TerminatorKind::Abort
            | rustc_middle::mir::terminator::TerminatorKind::Return
            | rustc_middle::mir::terminator::TerminatorKind::Unreachable
            | rustc_middle::mir::terminator::TerminatorKind::Drop {
                place: _,
                target: _,
                unwind: _,
            }
            | rustc_middle::mir::terminator::TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target: _,
                cleanup: _,
            }
            | rustc_middle::mir::terminator::TerminatorKind::FalseEdge {
                real_target: _,
                imaginary_target: _,
            }
            | rustc_middle::mir::terminator::TerminatorKind::FalseUnwind {
                real_target: _,
                unwind: _,
            }
            | rustc_middle::mir::terminator::TerminatorKind::DropAndReplace {
                place: _,
                value: _,
                target: _,
                unwind: _,
            } => {
                // Nothing to do
            }
            rustc_middle::mir::terminator::TerminatorKind::Call {
                func,
                args,
                destination: _,
                cleanup: _,
                from_hir_call: _,
                fn_span,
            } => {
                trace!("terminator: Call\n{:?}", &terminator);
                trace!("terminator:Call:func: {:?}", func);

                let (fid, substs) = get_fun_from_operand(func).expect("Expected a function call");
                trace!("terminator:Call:fid {:?}", fid);

                let name = function_def_id_to_name(tcx, fid);
                trace!("called function: name: {:?}", name);

                // We may need to filter the types and arguments, if the type
                // is considered primitive
                let (used_types, used_args, is_prim) = if fid.is_local() {
                    // We probably do not need to check if the function is local...
                    (Option::None, Option::None, false)
                } else {
                    match assumed::function_to_info(&name) {
                        Option::Some(used) => {
                            // The function is primitive
                            (
                                Option::Some(used.used_type_params),
                                Option::Some(used.used_args),
                                true,
                            )
                        }
                        Option::None => {
                            // The function is non-primitive (i.e., external)
                            (Option::None, Option::None, false)
                        }
                    }
                };

                // Add this function to the list of dependencies, only if
                // it is non-primitive
                if !is_prim {
                    fn_decl.deps_funs.insert(fid);
                }

                // Register the types given as parameters.
                register_mir_substs(
                    crate_info,
                    rdecls,
                    sess,
                    tcx,
                    &fn_span,
                    &mut fn_decl.deps_tys,
                    used_types,
                    &substs,
                )?;

                // Filter and register the argument types.
                // There is something very annoying, which is that MIR is quite
                // low level.
                // Very specifically, when introducing `box_free`, rustc introduces
                // something of the following form:
                // ```
                // _9 = alloc::alloc::box_free::<T, std::alloc::Global>(
                //   move (_4.0: std::ptr::Unique<T>),
                //   move (_4.1: std::alloc::Global)) -> bb3;
                // ```
                // We don't support unique pointers, so we have to ignore the
                // arguments in this case (and the `box_free` case has a
                // special treatment when translating function bodies).
                // Note that the type parameters have already been registered.
                if !name.equals_ref_name(&assumed::BOX_FREE_NAME) {
                    let args: Vec<&rustc_middle::mir::Operand<'_>> = match used_args {
                        Option::None => args.iter().collect(),
                        Option::Some(used_args) => {
                            // Filter
                            trace!("args: {:?}, used_args: {:?}", args, used_args);
                            assert!(args.len() == used_args.len());
                            args.iter()
                                .zip(used_args.into_iter())
                                .filter_map(|(param, used)| if used { Some(param) } else { None })
                                .collect()
                        }
                    };
                    for a in args.into_iter() {
                        trace!("terminator: Call: arg: {:?}", a);

                        let ty = a.ty(&body.local_decls, tcx);
                        register_mir_ty(
                            crate_info,
                            rdecls,
                            sess,
                            tcx,
                            &fn_span,
                            &mut fn_decl.deps_tys,
                            &ty,
                        )?;
                    }
                }

                // Note that we don't need to register the "bare" function
                // signature: all the types it contains are already covered
                // by the type arguments and the parameters.

                // Lookup the function definition, if it is local (i.e.: is
                // defined in the current crate).
                let hir_map = tcx.hir();
                let f_node = hir_map.get_if_local(fid);
                match f_node {
                    Some(f_node) => {
                        trace!("Function is local");
                        match f_node {
                            rustc_hir::Node::Item(f_item) => {
                                trace!("Item");
                                assert!(is_fn_decl(f_item));
                                register_hir_item(crate_info, rdecls, sess, tcx, false, f_item)?;
                            }
                            rustc_hir::Node::ImplItem(impl_item) => {
                                trace!("Impl item");
                                // [register_hir_impl_item doesn't check if the item
                                // has already been registered, so we need to
                                // check it before calling it.
                                register_hir_impl_item(crate_info, rdecls, sess, tcx, impl_item)?;
                            }
                            _ => {
                                unreachable!();
                            }
                        }
                    }
                    None => {
                        trace!("Function external");
                        // Register
                        // Rk.: [register_non_local_function] checks if the def
                        // id has already been registered, and inserts it in the
                        // decls set if necessary (not the same behaviour as
                        // the "local" case).
                        register_non_local_function(crate_info, rdecls, sess, tcx, fid, name)?;
                    }
                }
            }
            rustc_middle::mir::terminator::TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => {
                trace!("terminator: Yield");
                span_err(
                    sess,
                    terminator.source_info.span.clone(),
                    "Yield is not supported",
                );
            }
            rustc_middle::mir::terminator::TerminatorKind::GeneratorDrop => {
                trace!("terminator: GeneratorDrop");
                span_err(
                    sess,
                    terminator.source_info.span.clone(),
                    "Generators are not supported",
                );
            }
            rustc_middle::mir::terminator::TerminatorKind::InlineAsm {
                template: _,
                operands: _,
                options: _,
                line_spans: _,
                destination: _,
                cleanup: _,
            } => {
                trace!("terminator: InlineASM");
                span_err(
                    sess,
                    terminator.source_info.span.clone(),
                    "Inline ASM is not supported",
                );
            }
        }
    }

    Ok(())
}

/// Register a function.
/// The caller must have checked if the def_id has been registered before, and
/// must call this function only if it was not the case, and after having added
/// the def_id to the list of registered ids.
fn register_local_function(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    def_id: LocalDefId,
) -> Result<()> {
    trace!("{:?}", def_id);

    let ldef_id = def_id;
    let def_id = def_id.to_def_id();

    // Check the generics - TODO: we check this here and in translate_functions_to_im
    generics::check_function_generics(tcx, def_id);

    // Initialize the function declaration that we will register in the
    // declarations map, and in particular its list of dependencies that
    // we will progressively fill during exploration.
    let mut fn_decl = RegisteredFunDeclaration::new(def_id);

    // We explore the function definition only if it is not in a module flagged
    // as opaque
    let name = function_def_id_to_name(tcx, def_id);
    if name.is_in_modules(&crate_info.crate_name, &crate_info.opaque) {
        // The function is opaque
        // Store the function declaration in the declaration map
        rdecls.funs.insert(def_id, fn_decl);
        rdecls.opaque_funs.insert(def_id);
        return Ok(());
    }

    // The function is not opaque
    // Explore the body
    register_local_function_body(crate_info, rdecls, sess, tcx, ldef_id, &mut fn_decl)?;

    // Store the function declaration in the declarations map
    rdecls.funs.insert(def_id, fn_decl);

    return Ok(());
}

/// General function to register a MIR item. It is called on all the top-level
/// items. This includes: crate inclusions and `use` instructions (which are
/// ignored), but also type and functions declarations.
/// Note that this function checks if the item has been registered, and adds
/// its def_id to the list of registered items otherwise.
fn register_hir_item(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    top_item: bool,
    item: &Item,
) -> Result<()> {
    trace!("{:?}", item);

    // First check if the item definition has already been registered
    // (or is currently being registered). If it is the case, return to
    // prevent cycles. If not registered yet, do not immediately add it:
    // it may be an item we won't translate (`use module`, `extern crate`...).
    let def_id = item.def_id.to_def_id();
    if rdecls.decls.contains(&def_id) {
        return Ok(());
    }

    // The annoying thing is that when iterating over the items in a crate, we
    // iterate over *all* the items, which is annoying with regards to the
    // *opaque* modules: we see all the definitions which are in there, and
    // not only those which are transitively reachable from the root.
    // Because of this, we need the following check: if the item is a "top"
    // item (not an item transitively reachable from an item which is not
    // opaque) and inside an opaque module (or sub-module), we ignore it.
    if top_item {
        match hir_item_to_name(tcx, item) {
            Option::None => {
                // This kind of item is to be ignored
                return Ok(());
            }
            Option::Some(item_name) => {
                if item_name.is_in_modules(&crate_info.crate_name, &crate_info.opaque) {
                    return Ok(());
                }
            }
        }
    }

    // Case disjunction on the kind. Note that here we retrieve the HIR items,
    // but then work on the MIR.
    match &item.kind {
        ItemKind::TyAlias(_, _) => {
            // We ignore the type aliases - it seems they are inlined
            return Ok(());
        }
        ItemKind::Enum(_, _) | ItemKind::Struct(_, _) => {
            rdecls.decls.insert(def_id);
            return register_hir_type(crate_info, rdecls, sess, tcx, item, def_id);
        }
        ItemKind::OpaqueTy(_) => unimplemented!(),
        ItemKind::Union(_, _) => unimplemented!(),
        ItemKind::Fn(_, _, _) => {
            rdecls.decls.insert(def_id);
            return register_local_function(crate_info, rdecls, sess, tcx, item.def_id);
        }
        ItemKind::Impl(impl_block) => {
            trace!("impl");
            // Sanity checks
            translate_functions_to_im::check_impl_item(impl_block);

            // Explore the items
            let hir_map = tcx.hir();
            for impl_item_ref in impl_block.items {
                // impl_item_ref only gives the reference of the impl item:
                // we need to look it up
                let impl_item = hir_map.impl_item(impl_item_ref.id);

                register_hir_impl_item(crate_info, rdecls, sess, tcx, impl_item)?;
            }
            return Ok(());
        }
        ItemKind::Use(_, _) => {
            // Ignore
            trace!("use");
            return Ok(());
        }
        ItemKind::ExternCrate(_) => {
            // Ignore
            trace!("extern crate");
            return Ok(());
        }
        ItemKind::Mod(module) => {
            trace!("module");

            // Explore the module, only if it was not marked as "opaque"
            // TODO: we may want to accumulate the set of modules we found,
            // to check that all the opaque modules given as arguments actually
            // exist
            trace!("{:?}", def_id);
            let module_name = module_def_id_to_name(tcx, def_id);
            let opaque = module_name.is_in_modules(&crate_info.crate_name, &crate_info.opaque);
            if opaque {
                // Ignore
                trace!("Ignoring module [{}] because marked as opaque", module_name);
                return Ok(());
            } else {
                trace!("Diving into module [{}]", module_name);
                let hir_map = tcx.hir();
                for item_id in module.item_ids {
                    // Lookup and register the item
                    let item = hir_map.item(*item_id);
                    register_hir_item(crate_info, rdecls, sess, tcx, false, item)?;
                }
                return Ok(());
            }
        }
        _ => {
            unimplemented!("{:?}", item.kind);
        }
    }
}

/// Register an impl item (an item defined in an `impl` block)
///
/// Note that this function checks if the item has been registered, and adds
/// its def_id to the list of registered items otherwise.
fn register_hir_impl_item(
    crate_info: &CrateInfo,
    rdecls: &mut RegisteredDeclarations,
    sess: &Session,
    tcx: TyCtxt,
    impl_item: &ImplItem,
) -> Result<()> {
    // Check if the item has already been registered
    let def_id = impl_item.def_id.to_def_id();
    if rdecls.decls.contains(&def_id) {
        return Ok(());
    }

    // TODO: make proper error message
    assert!(impl_item.defaultness == Defaultness::Final);

    // Match on the impl item kind
    match &impl_item.kind {
        ImplItemKind::Const(_, _) => unimplemented!(),
        ImplItemKind::TyAlias(_) => unimplemented!(),
        ImplItemKind::Fn(_, _) => {
            let local_def_id = impl_item.def_id;
            let def_id = local_def_id.to_def_id();
            rdecls.decls.insert(def_id);
            register_local_function(crate_info, rdecls, sess, tcx, local_def_id)
        }
    }
}

/// General function to register the declarations in a crate.
pub fn register_crate(
    crate_info: &CrateInfo,
    sess: &Session,
    tcx: TyCtxt,
) -> Result<RegisteredDeclarations> {
    let mut registered_decls = RegisteredDeclarations::new();

    // TODO: in order to have a good ordering when extracting the information
    // from a crate with several modules, it would be better to not register
    // def ids immediately upon finding them, put rather to push them on a
    // stack, so that we can try to explore them in the order in which they
    // are defined in their respective modules.

    // The way rustc works is as follows:
    // - we call it on the root of the crate (for instance "main.rs"), and it
    //   explores all the files from there (typically listed through statements
    //   of the form "mod MODULE_NAME")
    // - the other files in the crate are Module items in the HIR graph
    for item in tcx.hir().items() {
        register_hir_item(crate_info, &mut registered_decls, sess, tcx, true, item)?;
    }
    return Ok(registered_decls);
}
