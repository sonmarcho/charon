use crate::assumed;
use crate::common::*;
use crate::generics;
use crate::get_mir::EXTRACT_CONSTANTS_AT_TOP_LEVEL;
use crate::names::Name;
use crate::names::{
    function_def_id_to_name, global_def_id_to_name, hir_item_to_name, module_def_id_to_name,
    type_def_id_to_name,
};
use crate::translate_functions_to_im;
use hashlink::LinkedHashMap;
use linked_hash_set::LinkedHashSet;
use rustc_hir::{
    def_id::DefId, def_id::LocalDefId, Defaultness, ImplItem, ImplItemKind, Item, ItemKind,
};
use rustc_middle::mir;
use rustc_middle::ty::{AdtDef, Ty, TyCtxt, TyKind};
use rustc_session::Session;
use rustc_span::Span;
use std::collections::HashSet;

pub struct CrateInfo {
    pub crate_name: String,
    pub opaque_mods: HashSet<String>,
}

impl CrateInfo {
    fn has_opaque_decl(&self, name: &Name) -> bool {
        name.is_in_modules(&self.crate_name, &self.opaque_mods)
    }
}

/// All kind of supported Rust top-level declarations.
/// const and static variables are merged together in the global kind.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum DeclKind {
    Type,
    Fun,
    Global,
}

pub type DeclDependencies = LinkedHashSet<DefId>;

/// A registered declaration, listing its dependencies.
#[derive(Debug)]
pub struct Declaration {
    // The declaration may be local or extern (id.is_local()).
    pub id: DefId,
    pub kind: DeclKind,
    // The IDs of the declarations its body depends on.
    // None if opaque (it means that the body is unavailable).
    pub deps: Option<DeclDependencies>,
}

impl Declaration {
    fn new_opaque(id: DefId, kind: DeclKind) -> Declaration {
        Declaration {
            id,
            kind,
            deps: None,
        }
    }

    fn new_visible(id: DefId, kind: DeclKind, deps: DeclDependencies) -> Declaration {
        Declaration {
            id,
            kind,
            deps: Some(deps),
        }
    }

    pub fn is_transparent(&self) -> bool {
        self.deps.is_some()
    }
}

fn get_decl_name(tcx: TyCtxt, kind: DeclKind, id: DefId) -> Name {
    match kind {
        DeclKind::Type => type_def_id_to_name(tcx, id),
        DeclKind::Fun => function_def_id_to_name(tcx, id),
        DeclKind::Global => global_def_id_to_name(tcx, id),
    }
}

fn is_primitive_decl(kind: DeclKind, id: DefId, name: &Name) -> bool {
    if id.is_local() {
        return false;
    }
    match kind {
        DeclKind::Type => assumed::type_to_used_params(&name).is_some(),
        DeclKind::Fun => assumed::function_to_info(&name).is_some(),
        DeclKind::Global => false,
    }
}

fn check_decl_generics(kind: DeclKind, tcx: TyCtxt, id: DefId) {
    match kind {
        DeclKind::Type => generics::check_type_generics(tcx, id),
        DeclKind::Fun => generics::check_function_generics(tcx, id),
        DeclKind::Global => generics::check_global_generics(tcx, id),
    }
}

fn new_opaque_declaration(
    tcx: TyCtxt,
    id: DefId,
    kind: DeclKind,
    name: &Name,
) -> Option<Declaration> {
    trace!("opaque declaration {}", name);

    if is_primitive_decl(kind, id, name) {
        return None;
    }

    // TODO: we check this here and in translate_types
    check_decl_generics(kind, tcx, id);
    Some(Declaration::new_opaque(id, kind))
}

struct RegisterContext<'a, 'b, 'c> {
    rustc: TyCtxt<'a>,
    sess: &'b Session,
    crate_info: &'c CrateInfo,
}

pub type RegisteredDeclarations = LinkedHashMap<DefId, Declaration>;

/// Structure used to register declarations: see
/// [DeclarationsRegister::register_opaque_declaration] and
/// [DeclarationsRegister::register_visible_declaration].
struct DeclarationsRegister {
    decl_ids: LinkedHashSet<DefId>,
    decls: RegisteredDeclarations,
}

impl DeclarationsRegister {
    fn new() -> DeclarationsRegister {
        DeclarationsRegister {
            decl_ids: LinkedHashSet::new(),
            decls: RegisteredDeclarations::new(),
        }
    }

    /// Indicates if the declaration is being (or has been) added.
    fn knows(&self, id: &DefId) -> bool {
        self.decl_ids.contains(id)
    }

    /// The declarations are registered in two steps:
    /// When their exploration begins, we must first add their id.
    /// This is done to prevent cycles while registering declarations.
    ///
    /// Should not be called outside [DeclarationsRegister]'s methods:
    /// Use either [DeclarationsRegister::register_opaque_declaration]
    /// or [DeclarationsRegister::register_visible_declaration] instead.
    fn add_begin(&mut self, id: DefId) {
        assert!(self.decl_ids.insert(id), "Already knows {:?}", id);
    }

    /// Finalize the registering of a declaration.
    ///
    /// Should not be called outside [DeclarationsRegister]'s methods:
    /// Use either [DeclarationsRegister::register_opaque_declaration]
    /// or [DeclarationsRegister::register_visible_declaration] instead.
    fn add_end(&mut self, decl: Declaration) {
        let id = decl.id;
        assert!(self.knows(&id));

        assert!(
            self.decls.insert(id, decl).is_none(),
            "Registered the same declaration {:?} twice",
            id
        );
    }

    /// Does not explore further the declaration content:
    /// If the declaration was unknown, registers it without dependencies.
    fn register_opaque_declaration(&mut self, tcx: TyCtxt, id: DefId, kind: DeclKind, name: &Name) {
        if self.knows(&id) {
            return;
        }

        new_opaque_declaration(tcx, id, kind, name).map(|decl| {
            self.add_begin(id);
            self.add_end(decl);
        });
    }

    /// Registers a declaration and its dependencies recursively.
    /// Only works on local declarations for now.
    /// The visitor takes `&mut self` to avoid a double borrow.
    fn register_visible_declaration<
        F: FnOnce(&mut DeclarationsRegister) -> Result<DeclDependencies>,
    >(
        &mut self,
        ctx: &RegisterContext,
        local_id: LocalDefId,
        kind: DeclKind,
        list_dependencies: F,
    ) -> Result<()> {
        trace!("{:?}", local_id);

        let id = local_id.to_def_id();
        self.add_begin(id);

        let name = get_decl_name(ctx.rustc, kind, id);

        // Only local declarations are supported for now, it should not be primitive.
        if is_primitive_decl(kind, id, &name) {
            unreachable!();
        }

        // TODO: we check this here and in translate_functions_to_im
        check_decl_generics(kind, ctx.rustc, id);

        // We don't explore declarations in opaque modules.
        if ctx.crate_info.has_opaque_decl(&name) {
            self.add_end(Declaration::new_opaque(id, kind));
            return Ok(());
        }

        let deps = list_dependencies(self)?;
        self.add_end(Declaration::new_visible(id, kind, deps));
        return Ok(());
    }

    /// Returns all registered declarations.
    /// Verifies that no known id or dependency is missing.
    fn get_declarations(self) -> RegisteredDeclarations {
        for id in self.decl_ids.iter() {
            assert!(
                self.decls.contains_key(id),
                "Did not register known id {:?}",
                id
            );
        }
        for (_, decl) in &self.decls {
            for id in decl.deps.iter().flatten() {
                assert!(
                    self.decls.contains_key(id),
                    "Did not register dependency id {:?} from {:?}",
                    id,
                    decl.id
                )
            }
        }
        self.decls
    }
}

/// Register a HIR type.
/// This function is called when processing top-level declarations. It mostly
/// delegates the work to functions operating on the MIR (and once in MIR we
/// stay in MIR).
fn register_hir_type(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
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
            let adt = ctx.rustc.adt_def(def_id);
            return register_local_adt(ctx, decls, adt);
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
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    adt: &AdtDef,
) -> Result<()> {
    trace!("> adt: {:?}", adt);

    // First, retrieve the HIR definition - this function may have been
    // called from MIR code, which is why we don't take an item or a HIR
    // definition as parameter. We use it only for the span, to report
    // precise error messages to the user.
    let hir_map = ctx.rustc.hir();
    let item = if let rustc_hir::Node::Item(item) = hir_map.get_if_local(adt.did).unwrap() {
        item
    } else {
        unreachable!();
    };

    let local_id = adt.did.as_local().unwrap();
    decls.register_visible_declaration(ctx, local_id, DeclKind::Type, |decls| {
        // Use a dummy substitution to instantiate the type parameters
        let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(ctx.rustc, adt.did);

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

        let mut ty_deps = DeclDependencies::new();
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
                let ty = field_def.ty(ctx.rustc, substs);
                trace!("ty");
                register_mir_ty(ctx, decls, var_span, &mut ty_deps, &ty)?;
            }

            i += 1;
        }
        Ok(ty_deps)
    })
}

/// Auxiliary function to register a list of type parameters.
fn register_mir_substs<'tcx>(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    span: &Span,
    ty_deps: &mut DeclDependencies,
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
                register_mir_ty(ctx, decls, span, ty_deps, &param_ty)?;
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
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    span: &Span,
    ty_deps: &mut DeclDependencies,
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
            let name = type_def_id_to_name(ctx.rustc, adt.did);

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
                ty_deps.insert(adt.did);
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
                register_mir_substs(ctx, decls, span, ty_deps, used_params, substs)?;

                // Register the external ADT as an opaque declaration.
                // In the future, we will explore the ADT, to reveal its public
                // information (public fields in case of a structure, variants in
                // case of a public enumeration).
                decls.register_opaque_declaration(ctx.rustc, adt.did, DeclKind::Type, &name);
                return Ok(());
            } else {
                // Explore the type parameters instantiation
                register_mir_substs(ctx, decls, span, ty_deps, Option::None, substs)?;

                // Explore the ADT, if we haven't already registered it
                // Check if registered
                if decls.knows(&adt.did) {
                    trace!("Adt already registered");
                    return Ok(());
                }
                trace!("Adt not registered");

                // Register and explore
                return register_local_adt(ctx, decls, adt);
            }
        }
        TyKind::Array(ty, const_param) => {
            trace!("Array");

            register_mir_ty(ctx, decls, span, ty_deps, ty)?;
            return register_mir_ty(ctx, decls, span, ty_deps, &const_param.ty);
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            return register_mir_ty(ctx, decls, span, ty_deps, ty);
        }
        TyKind::Ref(_, ty, _) => {
            trace!("Ref");

            return register_mir_ty(ctx, decls, span, ty_deps, ty);
        }
        TyKind::Tuple(substs) => {
            trace!("Tuple");

            for param in substs.iter() {
                let param_ty = param.expect_ty();
                register_mir_ty(ctx, decls, span, ty_deps, &param_ty)?;
            }

            return Ok(());
        }

        TyKind::RawPtr(_) => {
            // A raw pointer
            trace!("RawPtr");
            span_err(ctx.sess, span.clone(), "raw pointers are not supported");
            return Err(());
        }
        TyKind::Foreign(_) => {
            // A raw pointer
            trace!("Foreign");
            span_err(ctx.sess, span.clone(), "FFI types are not supported");
            return Err(());
        }
        TyKind::Infer(_) => {
            trace!("Infer");
            span_err(
                ctx.sess,
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
                register_mir_ty(ctx, decls, span, ty_deps, &param_ty)?;
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
            span_err(ctx.sess, span.clone(), "Generators are not supported");
            return Err(());
        }

        TyKind::Error(_) => {
            trace!("Error");
            span_err(
                ctx.sess,
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
            // A type parameter, for example `T` in `fn f<T>(x: T) {}`
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
    op: &mir::Operand<'tcx>,
) -> Option<(DefId, rustc_middle::ty::subst::SubstsRef<'tcx>)> {
    let fun_ty = op.constant().unwrap().literal.ty();
    match fun_ty.kind() {
        TyKind::FnDef(def_id, substs) => return Some((*def_id, substs)),
        _ => {
            return None;
        }
    }
}

// Visits all statements and terminators of the body blocks.
fn visit_block<'tcx, V: mir::visit::Visitor<'tcx>>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    mut visitor: V,
) {
    use mir::visit::MirVisitable;

    // The location is not used in the visitor, so we pass an arbitrary one there.
    for statement in block.statements.iter() {
        statement.apply(mir::Location::START, &mut visitor);
    }
    block.terminator().apply(mir::Location::START, &mut visitor);
}

fn visit_globals<'tcx>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    f: &mut dyn FnMut(&'tcx rustc_middle::ty::Const<'tcx>),
) {
    // Implement the visitor trait for the given lambda.
    // It may be possible to avoid erasing f type with more rust-fu.
    struct ConstVisitor<'tcx, 'f> {
        f: &'f mut dyn FnMut(&'tcx rustc_middle::ty::Const<'tcx>),
    }
    impl<'tcx, 'f> mir::visit::Visitor<'tcx> for ConstVisitor<'tcx, 'f> {
        fn visit_const(&mut self, c: &&'tcx rustc_middle::ty::Const<'tcx>, _: mir::Location) {
            (self.f)(c);
        }
    }
    visit_block(block, ConstVisitor { f });
}

fn visit_global_dependencies<'tcx, F: FnMut(DefId)>(
    block: &'tcx mir::BasicBlockData<'tcx>,
    mut f: F,
) {
    visit_globals(block, &mut |c| match c.val {
        rustc_middle::ty::ConstKind::Value(_) => (),
        rustc_middle::ty::ConstKind::Unevaluated(uv) => {
            f(uv.def.did);
        }
        rustc_middle::ty::ConstKind::Param(_)
        | rustc_middle::ty::ConstKind::Infer(_)
        | rustc_middle::ty::ConstKind::Bound(_, _)
        | rustc_middle::ty::ConstKind::Placeholder(_)
        | rustc_middle::ty::ConstKind::Error(_) => {
            unimplemented!();
        }
    });
}

fn register_dependency_expression(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    id: DefId,
    kind: DeclKind,
    name: &Name,
) -> Result<()> {
    match ctx.rustc.hir().get_if_local(id) {
        None => {
            trace!("external expression");

            // Register the external expression as an opaque one.
            decls.register_opaque_declaration(ctx.rustc, id, kind, &name);
            Ok(())
        }
        Some(node) => {
            trace!("local expression");
            match node {
                rustc_hir::Node::Item(item) => {
                    trace!("Item");
                    register_hir_item(ctx, decls, false, item)
                }
                rustc_hir::Node::ImplItem(impl_item) => {
                    trace!("Impl item");
                    register_hir_impl_item(ctx, decls, impl_item)
                }
                _ => {
                    unreachable!();
                }
            }
        }
    }
}

/// Register the identifiers found in a function or global body.
fn register_body(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    def_id: LocalDefId,
    deps: &mut DeclDependencies,
) -> Result<()> {
    // Retrieve the MIR code.
    let body = crate::get_mir::get_mir_for_def_id(ctx.rustc, def_id);

    // Visit the global dependencies if the MIR is not optimized.
    if EXTRACT_CONSTANTS_AT_TOP_LEVEL {
        // TODO: For now the order of dependencies export depend on the order
        // in which they are discovered. By storing their metadata, we would be
        // able to order them properly, without depending on the visit ordering.
        // Avoid registering globals in optimized MIR (they will be inlined).
        for b in body.basic_blocks().iter() {
            propagate_error(
                |f| visit_global_dependencies(b, f),
                |id| {
                    let name = global_def_id_to_name(ctx.rustc, id);

                    if is_primitive_decl(DeclKind::Global, id, &name) {
                        return Ok(());
                    }
                    if !deps.insert_if_absent(id) {
                        return Ok(());
                    }

                    trace!("added constant dependency {:?} -> {}", def_id, name);
                    register_dependency_expression(ctx, decls, id, DeclKind::Global, &name)
                },
            )?;
        }
    }

    // Start by registering the types found in the local variable declarations.
    // Note that those local variables include the parameters as well as the
    // return variable, and is thus enough to register the function signature.
    for v in body.local_decls.iter() {
        register_mir_ty(ctx, decls, &v.source_info.span, deps, &v.ty)?;
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
                mir::StatementKind::Assign(_)
                | mir::StatementKind::FakeRead(_)
                | mir::StatementKind::SetDiscriminant {
                    place: _,
                    variant_index: _,
                }
                | mir::StatementKind::StorageLive(_)
                | mir::StatementKind::StorageDead(_)
                | mir::StatementKind::AscribeUserType(_, _)
                | mir::StatementKind::Coverage(_)
                | mir::StatementKind::Nop => {
                    // Nothing to do
                }

                mir::StatementKind::CopyNonOverlapping(_) => {
                    trace!("Copy non overlapping");
                    span_err(
                        ctx.sess,
                        statement.source_info.span.clone(),
                        "Copy non overlapping not supported",
                    );
                }
                mir::StatementKind::Retag(_, _) => {
                    // retag statements are only used by MIRI, so we have nothing
                    // to do
                }
            }
        }

        // Terminator
        let terminator = block.terminator();
        match &terminator.kind {
            mir::terminator::TerminatorKind::Goto { target: _ }
            | mir::terminator::TerminatorKind::SwitchInt {
                discr: _,
                switch_ty: _,
                targets: _,
            }
            | mir::terminator::TerminatorKind::Resume
            | mir::terminator::TerminatorKind::Abort
            | mir::terminator::TerminatorKind::Return
            | mir::terminator::TerminatorKind::Unreachable
            | mir::terminator::TerminatorKind::Drop {
                place: _,
                target: _,
                unwind: _,
            }
            | mir::terminator::TerminatorKind::Assert {
                cond: _,
                expected: _,
                msg: _,
                target: _,
                cleanup: _,
            }
            | mir::terminator::TerminatorKind::FalseEdge {
                real_target: _,
                imaginary_target: _,
            }
            | mir::terminator::TerminatorKind::FalseUnwind {
                real_target: _,
                unwind: _,
            }
            | mir::terminator::TerminatorKind::DropAndReplace {
                place: _,
                value: _,
                target: _,
                unwind: _,
            } => {
                // Nothing to do
            }
            mir::terminator::TerminatorKind::Call {
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

                let name = function_def_id_to_name(ctx.rustc, fid);
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
                    deps.insert(fid);
                }

                // Register the types given as parameters.
                register_mir_substs(ctx, decls, &fn_span, deps, used_types, &substs)?;

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
                    let args: Vec<&mir::Operand<'_>> = match used_args {
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

                        let ty = a.ty(&body.local_decls, ctx.rustc);
                        register_mir_ty(ctx, decls, &fn_span, deps, &ty)?;
                    }
                }

                // Note that we don't need to register the "bare" function
                // signature: all the types it contains are already covered
                // by the type arguments and the parameters.

                register_dependency_expression(ctx, decls, fid, DeclKind::Fun, &name)?;
            }
            mir::terminator::TerminatorKind::Yield {
                value: _,
                resume: _,
                resume_arg: _,
                drop: _,
            } => {
                trace!("terminator: Yield");
                span_err(
                    ctx.sess,
                    terminator.source_info.span.clone(),
                    "Yield is not supported",
                );
            }
            mir::terminator::TerminatorKind::GeneratorDrop => {
                trace!("terminator: GeneratorDrop");
                span_err(
                    ctx.sess,
                    terminator.source_info.span.clone(),
                    "Generators are not supported",
                );
            }
            mir::terminator::TerminatorKind::InlineAsm {
                template: _,
                operands: _,
                options: _,
                line_spans: _,
                destination: _,
                cleanup: _,
            } => {
                trace!("terminator: InlineASM");
                span_err(
                    ctx.sess,
                    terminator.source_info.span.clone(),
                    "Inline ASM is not supported",
                );
            }
        }
    }

    Ok(())
}

/// Register an new expression (either a fonction or a global).
fn register_local_expression(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    local_id: LocalDefId,
    kind: DeclKind,
) -> Result<()> {
    decls.register_visible_declaration(ctx, local_id, kind, |decls| {
        let mut deps = DeclDependencies::new();
        register_body(ctx, decls, local_id, &mut deps)?;
        Ok(deps)
    })
}

/// General function to register a MIR item. It is called on all the top-level
/// items. This includes: crate inclusions and `use` instructions (which are
/// ignored), but also type and functions declarations.
/// Note that this function checks if the item has been registered, and adds
/// its def_id to the list of registered items otherwise.
fn register_hir_item(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    top_item: bool,
    item: &Item,
) -> Result<()> {
    trace!("{:?}", item);

    // First check if the item definition has already been registered
    // (or is currently being registered). If it is the case, return to
    // prevent cycles. If not registered yet, do not immediately add it:
    // it may be an item we won't translate (`use module`, `extern crate`...).
    let def_id = item.def_id.to_def_id();
    if decls.knows(&def_id) {
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
        match hir_item_to_name(ctx.rustc, item) {
            Option::None => {
                // This kind of item is to be ignored
                return Ok(());
            }
            Option::Some(item_name) => {
                if ctx.crate_info.has_opaque_decl(&item_name) {
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
            Ok(())
        }
        ItemKind::OpaqueTy(_) => unimplemented!(),
        ItemKind::Union(_, _) => unimplemented!(),
        ItemKind::Enum(_, _) | ItemKind::Struct(_, _) => {
            register_hir_type(ctx, decls, item, def_id)
        }
        ItemKind::Fn(_, _, _) => register_local_expression(ctx, decls, item.def_id, DeclKind::Fun),
        ItemKind::Const(_, _) | ItemKind::Static(_, _, _) => {
            if EXTRACT_CONSTANTS_AT_TOP_LEVEL {
                register_local_expression(ctx, decls, item.def_id, DeclKind::Global)
            } else {
                // Avoid registering globals in optimized MIR (they will be inlined).
                Ok(())
            }
        }

        ItemKind::Impl(impl_block) => {
            trace!("impl");
            // Sanity checks
            translate_functions_to_im::check_impl_item(impl_block);

            // Explore the items
            let hir_map = ctx.rustc.hir();
            for impl_item_ref in impl_block.items {
                // impl_item_ref only gives the reference of the impl item:
                // we need to look it up
                let impl_item = hir_map.impl_item(impl_item_ref.id);

                register_hir_impl_item(ctx, decls, impl_item)?;
            }
            Ok(())
        }
        ItemKind::Use(_, _) => {
            // Ignore
            trace!("use");
            Ok(())
        }
        ItemKind::ExternCrate(_) => {
            // Ignore
            trace!("extern crate");
            Ok(())
        }
        ItemKind::Mod(module) => {
            trace!("module");

            // Explore the module, only if it was not marked as "opaque"
            // TODO: we may want to accumulate the set of modules we found,
            // to check that all the opaque modules given as arguments actually
            // exist
            trace!("{:?}", def_id);
            let module_name = module_def_id_to_name(ctx.rustc, def_id);
            let opaque = ctx.crate_info.has_opaque_decl(&module_name);
            if opaque {
                // Ignore
                trace!("Ignoring module [{}] because marked as opaque", module_name);
                Ok(())
            } else {
                trace!("Diving into module [{}]", module_name);
                let hir_map = ctx.rustc.hir();
                for item_id in module.item_ids {
                    // Lookup and register the item
                    let item = hir_map.item(*item_id);
                    register_hir_item(ctx, decls, false, item)?;
                }
                Ok(())
            }
        }
        _ => {
            unimplemented!("{:?}", item.kind);
        }
    }
}

/// Register an impl item (an item defined in an `impl` block).
fn register_hir_impl_item(
    ctx: &RegisterContext,
    decls: &mut DeclarationsRegister,
    impl_item: &ImplItem,
) -> Result<()> {
    // Check if the item has already been registered
    let def_id = impl_item.def_id.to_def_id();
    if decls.knows(&def_id) {
        return Ok(());
    }

    // TODO: make proper error message
    assert!(impl_item.defaultness == Defaultness::Final);

    // Match on the impl item kind
    match &impl_item.kind {
        ImplItemKind::Const(_, _) => unimplemented!(),
        ImplItemKind::TyAlias(_) => unimplemented!(),
        ImplItemKind::Fn(_, _) => {
            let local_id = impl_item.def_id;
            register_local_expression(ctx, decls, local_id, DeclKind::Fun)
        }
    }
}

/// General function to register the declarations in a crate.
pub fn register_crate(
    crate_info: &CrateInfo,
    sess: &Session,
    tcx: TyCtxt,
) -> Result<RegisteredDeclarations> {
    let ctx = RegisterContext {
        rustc: tcx,
        crate_info,
        sess,
    };
    let mut decls = DeclarationsRegister::new();

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
        register_hir_item(&ctx, &mut decls, true, item)?;
    }
    Ok(decls.get_declarations())
}
