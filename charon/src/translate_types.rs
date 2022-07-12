use crate::assumed;
use crate::common::*;
use crate::formatter::Formatter;
use crate::generics;
use crate::id_vector::ToUsize;
use crate::names::type_def_id_to_name;
use crate::regions_hierarchy;
use crate::regions_hierarchy::TypesConstraintsMap;
use crate::reorder_decls::DeclarationGroup;
use crate::rust_to_local_ids::*;
use crate::types as ty;
use crate::types::TypeDeclId;
use im;
use im::Vector;
use rustc_hir::def_id::DefId;
use rustc_middle::mir::Mutability;
use rustc_middle::ty::TyCtxt;
use rustc_middle::ty::{Ty, TyKind};

/// Translation context for type definitions
#[derive(Clone)]
pub struct TypeTransContext<'ctx> {
    /// The type definitions - TODO: rename to type_defs
    pub types: &'ctx ty::TypeDecls,
    /// Ordered declarations allowing to convert id to and from rid.
    decls: &'ctx OrderedDecls,
}

impl<'ctx> TypeTransContext<'ctx> {
    pub fn new(types: &'ctx ty::TypeDecls, decls: &'ctx OrderedDecls) -> Self {
        Self { types, decls }
    }

    pub fn get_id(&self, rid: DefId) -> TypeDeclId::Id {
        *self.decls.type_rid_to_id.get(&rid).unwrap()
    }
}

/// Auxiliary definition used to format definitions.
struct TypeDeclFormatter<'a, 'ctx> {
    tt_ctx: &'a TypeTransContext<'ctx>,
    /// The region parameters of the definition we are printing (needed to
    /// correctly pretty print region var ids)
    region_params: &'a ty::RegionVarId::Vector<ty::RegionVar>,
    /// The type parameters of the definition we are printing (needed to
    /// correctly pretty print type var ids)
    type_params: &'a ty::TypeVarId::Vector<ty::TypeVar>,
}

impl<'ctx> Formatter<ty::TypeDeclId::Id> for TypeTransContext<'ctx> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.types.format_object(id)
    }
}

impl<'a, 'ctx> Formatter<ty::RegionVarId::Id> for TypeDeclFormatter<'a, 'ctx> {
    fn format_object(&self, id: ty::RegionVarId::Id) -> String {
        // Lookup the region parameter
        let v = self.region_params.get(id).unwrap();
        // Format
        v.to_string()
    }
}

impl<'a, 'ctx> Formatter<ty::TypeVarId::Id> for TypeDeclFormatter<'a, 'ctx> {
    fn format_object(&self, id: ty::TypeVarId::Id) -> String {
        // Lookup the type parameter
        let v = self.type_params.get(id).unwrap();
        // Format
        v.to_string()
    }
}

impl<'a, 'ctx> Formatter<&ty::Region<ty::RegionVarId::Id>> for TypeDeclFormatter<'a, 'ctx> {
    fn format_object(&self, r: &ty::Region<ty::RegionVarId::Id>) -> String {
        r.fmt_with_ctx(self)
    }
}

impl<'a, 'ctx> Formatter<&ty::ErasedRegion> for TypeDeclFormatter<'a, 'ctx> {
    fn format_object(&self, _: &ty::ErasedRegion) -> String {
        "".to_owned()
    }
}

impl<'a, 'ctx> Formatter<&ty::TypeDecl> for TypeDeclFormatter<'a, 'ctx> {
    fn format_object(&self, def: &ty::TypeDecl) -> String {
        def.fmt_with_ctx(self)
    }
}

impl<'a, 'ctx> Formatter<ty::TypeDeclId::Id> for TypeDeclFormatter<'a, 'ctx> {
    fn format_object(&self, id: ty::TypeDeclId::Id) -> String {
        self.tt_ctx.format_object(id)
    }
}

impl<'ctx> Formatter<&ty::TypeDecl> for TypeTransContext<'ctx> {
    fn format_object(&self, def: &ty::TypeDecl) -> String {
        // Create a type def formatter (which will take care of the
        // type parameters)
        let formatter = TypeDeclFormatter {
            tt_ctx: self,
            region_params: &def.region_params,
            type_params: &def.type_params,
        };
        formatter.format_object(def)
    }
}

pub fn translate_region_name(region: &rustc_middle::ty::RegionKind) -> Option<String> {
    match region {
        rustc_middle::ty::RegionKind::ReEarlyBound(r) => Some(r.name.to_ident_string()),
        rustc_middle::ty::RegionKind::ReLateBound(_, br) => match br.kind {
            rustc_middle::ty::BoundRegionKind::BrAnon(_) => None,
            rustc_middle::ty::BoundRegionKind::BrNamed(_, symbol) => Some(symbol.to_ident_string()),
            rustc_middle::ty::BoundRegionKind::BrEnv => Some("@env".to_owned()),
        },
        rustc_middle::ty::RegionKind::ReFree(r) => match r.bound_region {
            rustc_middle::ty::BoundRegionKind::BrAnon(_) => None,
            rustc_middle::ty::BoundRegionKind::BrNamed(_, symbol) => Some(symbol.to_ident_string()),
            rustc_middle::ty::BoundRegionKind::BrEnv => Some("@env".to_owned()),
        },
        _ => {
            unreachable!();
        }
    }
}

pub fn translate_non_erased_region<'tcx>(
    region_params: &im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id>,
    region: rustc_middle::ty::Region<'tcx>,
) -> ty::Region<ty::RegionVarId::Id> {
    match region {
        rustc_middle::ty::RegionKind::ReErased => unreachable!(),
        rustc_middle::ty::RegionKind::ReStatic => ty::Region::Static,
        _ => {
            let rid = region_params.get(region).unwrap();
            ty::Region::Var(*rid)
        }
    }
}

/// Translate a region which is expected to be erased.
///
/// The regions are expected to be erased inside the function bodies (i.e.:
/// we believe MIR uses regions only in the function signatures).
pub fn translate_erased_region<'tcx>(region: rustc_middle::ty::Region<'tcx>) -> ty::ErasedRegion {
    match region {
        rustc_middle::ty::RegionKind::ReErased => ty::ErasedRegion::Erased,
        _ => {
            unreachable!();
        }
    }
}

/// Translate a Ty.
///
/// Typically used in this module to translate the fields of a structure/
/// enumeration definition, or later to translate the type of a variable.
///
/// This function is also used in other modules, like
/// [`translate_functions`](crate::translate_functions).
/// This is the reason why the `type_params` parameter is quite general,
/// and links rust identifiers to types, rather than type variables (in
/// this module, this map should always link to the translation of the
/// type variables, but in other variables it may define a real substitution,
/// in the case the interpreter dives into functions for example).
///
/// Note that we take as parameter a function to translate regions, because
/// regions can be translated in several manners (non-erased region or erased
/// regions), in which case the return type is different.
pub fn translate_ty<R>(
    tcx: TyCtxt,
    trans_ctx: &TypeTransContext,
    region_translator: &dyn Fn(&rustc_middle::ty::RegionKind) -> R,
    type_params: &im::OrdMap<u32, ty::Ty<R>>,
    ty: &Ty,
) -> Result<ty::Ty<R>>
where
    R: Clone + Eq,
{
    trace!("{:?}", ty);
    match ty.kind() {
        TyKind::Bool => Ok(ty::Ty::Bool),
        TyKind::Char => Ok(ty::Ty::Char),
        TyKind::Int(int_ty) => Ok(ty::Ty::Integer(ty::IntegerTy::rust_int_ty_to_integer_ty(
            *int_ty,
        ))),
        TyKind::Uint(int_ty) => Ok(ty::Ty::Integer(ty::IntegerTy::rust_uint_ty_to_integer_ty(
            *int_ty,
        ))),
        TyKind::Str => Ok(ty::Ty::Str),
        TyKind::Float(_) => {
            trace!("Float");
            // This case should have been filtered during the registration phase
            unreachable!();
        }
        TyKind::Never => {
            return Ok(ty::Ty::Never);
        }

        TyKind::Adt(adt, substs) => {
            trace!("Adt: {:?}", adt.did);

            // Retrieve the list of used arguments
            let used_params = if adt.did.is_local() {
                Option::None
            } else {
                let name = type_def_id_to_name(tcx, adt.did);
                assumed::type_to_used_params(&name)
            };

            // Translate the type parameters instantiation
            let (regions, params) = translate_substs(
                tcx,
                trans_ctx,
                region_translator,
                type_params,
                used_params,
                substs,
            )?;

            // Retrieve the ADT identifier
            let def_id = translate_defid(tcx, trans_ctx, adt.did);

            // Return the instantiated ADT
            return Ok(ty::Ty::Adt(
                def_id,
                Vector::from(regions),
                Vector::from(params),
            ));
        }
        TyKind::Array(ty, _const_param) => {
            trace!("Array");

            let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, ty)?;
            return Ok(ty::Ty::Array(Box::new(ty)));
        }
        TyKind::Slice(ty) => {
            trace!("Slice");

            let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, ty)?;
            return Ok(ty::Ty::Slice(Box::new(ty)));
        }
        TyKind::Ref(region, ty, mutability) => {
            trace!("Ref");

            let region = region_translator(region);
            let ty = translate_ty(tcx, trans_ctx, region_translator, type_params, ty)?;
            let kind = match *mutability {
                Mutability::Not => ty::RefKind::Shared,
                Mutability::Mut => ty::RefKind::Mut,
            };
            return Ok(ty::Ty::Ref(region, Box::new(ty), kind));
        }
        TyKind::Tuple(substs) => {
            trace!("Tuple");

            let mut params = vec![];
            for param in substs.iter() {
                let param_ty = param.expect_ty();
                let param_ty =
                    translate_ty(tcx, trans_ctx, region_translator, type_params, &param_ty)?;
                params.push(param_ty);
            }

            return Ok(ty::Ty::Adt(
                ty::TypeId::Tuple,
                Vector::new(),
                Vector::from(params),
            ));
        }

        TyKind::FnPtr(_) => {
            trace!("FnPtr");
            unimplemented!();
        }
        TyKind::Param(param) => {
            // A type parameter, for example `T` in `fn f<T>(x : T) {}`.
            // Note that this type parameter may actually have been
            // instantiated (in our environment, we may map it to another
            // type): we just have to look it up.
            // Note that if we are using this function to translate a field
            // type in a type definition, it should actually map to a type
            // parameter.
            trace!("Param");

            // Retrieve the translation of the substituted type:
            let ty = type_params.get(&param.index).unwrap();

            return Ok(ty.clone());
        }

        // Below: those types should be unreachable: if such types are used in
        // the MIR, we should have found them and failed during the registration
        // phase.
        TyKind::RawPtr(_) => {
            trace!("RawPtr");
            unreachable!();
        }
        TyKind::Foreign(_) => {
            trace!("Foreign");
            unreachable!();
        }
        TyKind::Infer(_) => {
            trace!("Infer");
            unreachable!();
        }

        TyKind::FnDef(_, _) => {
            trace!("FnDef");
            unreachable!();
        }

        TyKind::Dynamic(_, _) => {
            trace!("Dynamic");
            unreachable!();
        }
        TyKind::Closure(_, _) => {
            trace!("Closure");
            unreachable!();
        }

        TyKind::Generator(_, _, _) | TyKind::GeneratorWitness(_) => {
            trace!("Generator");
            unreachable!();
        }

        TyKind::Error(_) => {
            trace!("Error");
            unreachable!();
        }
        TyKind::Projection(_) => {
            trace!("Projection");
            unreachable!();
        }
        TyKind::Opaque(_, _) => {
            trace!("Opaque");
            unreachable!();
        }
        TyKind::Bound(_, _) => {
            trace!("Bound");
            unreachable!();
        }
        TyKind::Placeholder(_) => {
            trace!("PlaceHolder");
            unreachable!();
        }
    }
}

/// Translate a signature type, where the regions are not erased and use region
/// variable ids.
/// Simply calls [`translate_ty`](translate_ty)
pub fn translate_sig_ty(
    tcx: TyCtxt,
    trans_ctx: &TypeTransContext,
    region_params: &im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id>,
    type_params: &im::OrdMap<u32, ty::RTy>,
    ty: &Ty,
) -> Result<ty::RTy> {
    translate_ty(
        tcx,
        trans_ctx,
        &|r| translate_non_erased_region(region_params, &r),
        type_params,
        ty,
    )
}

/// Translate a type where the regions are erased
/// Simply calls [`translate_ty`](translate_ty)
pub fn translate_ety(
    tcx: TyCtxt,
    trans_ctx: &TypeTransContext,
    type_params: &im::OrdMap<u32, ty::ETy>,
    ty: &Ty,
) -> Result<ty::ETy> {
    translate_ty(
        tcx,
        trans_ctx,
        &|r| translate_erased_region(&r),
        type_params,
        ty,
    )
}

fn translate_substs<'tcx, R>(
    tcx: TyCtxt,
    trans_ctx: &TypeTransContext,
    region_translator: &dyn Fn(&rustc_middle::ty::RegionKind) -> R,
    type_params: &im::OrdMap<u32, ty::Ty<R>>,
    used_params: Option<Vec<bool>>,
    substs: &rustc_middle::ty::subst::SubstsRef<'tcx>,
) -> Result<(Vec<R>, Vec<ty::Ty<R>>)>
where
    R: Clone + Eq,
{
    // Filter the parameters
    let mut param_i = 0;
    let substs: Vec<(rustc_middle::ty::subst::GenericArg<'_>, u32)> = match used_params {
        Option::None => substs
            .iter()
            .map(|p| {
                let i = param_i;
                param_i += 1;
                (p, i)
            })
            .collect(),
        Option::Some(used_params) => substs
            .iter()
            .zip(used_params.into_iter())
            .filter_map(|(param, used)| {
                let i = param_i;
                param_i += 1;
                if used {
                    Some((param, i))
                } else {
                    None
                }
            })
            .collect(),
    };

    let mut regions: Vec<R> = vec![];
    let mut params = vec![];
    for (param, param_i) in substs.iter() {
        trace!("Adt: param {}: {:?}", param_i, param);
        match param.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                let param_ty =
                    translate_ty(tcx, trans_ctx, region_translator, type_params, &param_ty)?;
                params.push(param_ty);
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                regions.push(region_translator(region));
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                unimplemented!();
            }
        }
    }

    Result::Ok((regions, params))
}

/// Translate a type def id
fn translate_defid(tcx: TyCtxt, trans_ctx: &TypeTransContext, def_id: DefId) -> ty::TypeId {
    trace!("{:?}", def_id);

    if def_id.is_local() {
        ty::TypeId::Adt(trans_ctx.get_id(def_id))
    } else {
        // Non-local: check if the type has primitive support

        // Retrieve the type name
        let name = type_def_id_to_name(tcx, def_id);

        match assumed::get_type_id_from_name(&name) {
            Option::Some(id) => {
                // The type has primitive support
                ty::TypeId::Assumed(id)
            }
            Option::None => {
                // The type is external
                ty::TypeId::Adt(trans_ctx.get_id(def_id))
            }
        }
    }
}

/// Helper type
struct TypeGenericsInfo<'tcx> {
    substs: rustc_middle::ty::subst::SubstsRef<'tcx>,
    region_params: Vec<ty::RegionVar>,
    region_params_map: im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id>,
    type_params: Vec<ty::TypeVar>,
    type_params_map: im::OrdMap<u32, ty::RTy>,
}

/// Auxiliary helper.
///
/// Translate the generics of a type definition.
/// Returns the translation, together with an instantiated MIR substitution,
/// which represents the generics on the MIR side (and is useful to translate
/// the body of the type...).
///
/// Rk.: this seems simpler in [translate_functions_to_im]. TODO: compare and
/// simplify/factorize?
fn translate_type_generics<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> TypeGenericsInfo<'tcx> {
    // Check the generics
    generics::check_type_generics(tcx, def_id);

    // Use a dummy substitution to instantiate the type parameters
    let substs = rustc_middle::ty::subst::InternalSubsts::identity_for_item(tcx, def_id);

    // Handle the region and type parameters:
    // - we need to know how many parameters there are
    // - we need to create a map linking the rust parameters to our pure
    //   parameters
    let mut region_params: Vec<ty::RegionVar> = vec![];
    let mut region_params_map: im::OrdMap<rustc_middle::ty::RegionKind, ty::RegionVarId::Id> =
        im::OrdMap::new();
    let mut region_params_counter = ty::RegionVarId::Generator::new();
    let mut type_params: Vec<ty::TypeVar> = vec![];
    let mut type_params_map: im::OrdMap<u32, ty::RTy> = im::OrdMap::new();
    let mut type_params_counter = ty::TypeVarId::Generator::new();
    for p in substs.iter() {
        match p.unpack() {
            rustc_middle::ty::subst::GenericArgKind::Type(param_ty) => {
                // The type should be a Param:
                match param_ty.kind() {
                    rustc_middle::ty::TyKind::Param(param_ty) => {
                        let type_var = ty::TypeVar {
                            index: type_params_counter.fresh_id(),
                            name: param_ty.name.to_ident_string(),
                        };
                        type_params.push(type_var.clone());
                        let type_var = ty::Ty::TypeVar(type_var.index);
                        type_params_map.insert(param_ty.index, type_var);
                    }
                    _ => {
                        panic!("Inconsistent state");
                    }
                }
            }
            rustc_middle::ty::subst::GenericArgKind::Lifetime(region) => {
                let name = translate_region_name(region);
                let t_region = ty::RegionVar {
                    index: region_params_counter.fresh_id(),
                    name: name,
                };
                region_params_map.insert(*region, t_region.index);
                region_params.push(t_region);
            }
            rustc_middle::ty::subst::GenericArgKind::Const(_) => {
                unimplemented!();
            }
        }
    }

    TypeGenericsInfo {
        substs,
        region_params,
        region_params_map,
        type_params,
        type_params_map,
    }
}

/// Translate one local type definition which has not been flagged as opaque.
fn translate_transparent_type<'tcx>(
    tcx: TyCtxt<'tcx>,
    decls: &OrderedDecls,
    type_defs: &mut ty::TypeDecls,
    trans_id: ty::TypeDeclId::Id,
    def_id: DefId,
    generics: &TypeGenericsInfo<'tcx>,
) -> Result<ty::TypeDeclKind> {
    trace!("{}", trans_id);

    // Initialize the type translation context
    let trans_ctx = TypeTransContext::new(&type_defs, &decls);

    // Retrieve the definition
    trace!("{:?}", def_id);
    let adt = tcx.adt_def(def_id);

    // Check and translate the generics (type and region parameters)
    let TypeGenericsInfo {
        substs,
        region_params: _,
        region_params_map,
        type_params: _,
        type_params_map,
    } = generics;

    // Explore the variants
    let mut var_id = ty::VariantId::Id::new(0); // Variant index
    let mut variants: Vec<ty::Variant> = vec![];
    for var_def in adt.variants.iter() {
        trace!("variant {}: {:?}", var_id, var_def);

        let mut fields: Vec<ty::Field> = vec![];
        let mut field_id = ty::FieldId::Id::new(0);
        /* This is for sanity: check that either all the fields have names, or
         * none of them has */
        let mut have_names: Option<bool> = Option::None;
        for field_def in var_def.fields.iter() {
            trace!("variant {}: field {}: {:?}", var_id, field_id, field_def);

            let ty = field_def.ty(tcx, substs);

            // Translate the field type
            let ty = translate_sig_ty(tcx, &trans_ctx, &region_params_map, &type_params_map, &ty)?;

            // Retrieve the field name.
            // Note that the only way to check if the user wrote the name or
            // if it is just an integer generated by rustc is by checking if
            // if is just made of numerals...
            let field_name = field_def.ident(tcx).name.to_ident_string();
            let field_name = {
                let field_id: std::result::Result<usize, std::num::ParseIntError> =
                    field_name.parse();
                match field_id {
                    std::result::Result::Ok(_) => None,
                    std::result::Result::Err(_) => Some(field_name),
                }
            };
            match &have_names {
                Option::None => {
                    have_names = match &field_name {
                        Option::None => Some(false),
                        Option::Some(_) => Some(true),
                    }
                }
                Option::Some(b) => {
                    assert!(*b == field_name.is_some());
                }
            };

            // Store the field
            let field = ty::Field {
                name: field_name.clone(),
                ty: ty,
            };
            fields.push(field);

            field_id.incr();
        }

        let variant_name = var_def.ident(tcx).name.to_ident_string();
        variants.push(ty::Variant {
            name: variant_name,
            fields: ty::FieldId::Vector::from(fields),
        });

        var_id.incr();
    }

    // Register the type
    let type_def_kind: ty::TypeDeclKind = match adt.adt_kind() {
        rustc_middle::ty::AdtKind::Struct => ty::TypeDeclKind::Struct(variants[0].fields.clone()),
        rustc_middle::ty::AdtKind::Enum => {
            ty::TypeDeclKind::Enum(ty::VariantId::Vector::from(variants))
        }
        rustc_middle::ty::AdtKind::Union => {
            // Should have been filtered during the registration phase
            unreachable!();
        }
    };

    Ok(type_def_kind)
}

/// Translate type definition.
///
/// Note that we translate the types one by one: we don't need to take into
/// account the fact that some types are mutually recursive at this point
/// (we will need to take that into account when generating the code in a file).
fn translate_type<'ctx>(
    tcx: TyCtxt,
    decls: &OrderedDecls,
    type_defs: &mut ty::TypeDecls,
    trans_id: ty::TypeDeclId::Id,
) -> Result<()> {
    let info = decls.decls_info.get(&AnyDeclId::Type(trans_id)).unwrap();

    // Check and translate the generics
    let generics = translate_type_generics(tcx, info.rid);

    // Check if the type is opaque or external, and delegate the translation
    // of the "body" to the proper function
    let kind = if !info.is_local() || !info.is_transparent {
        // Opaque types are:
        // - external types
        // - local types flagged as opaque
        ty::TypeDeclKind::Opaque
    } else {
        translate_transparent_type(tcx, decls, type_defs, trans_id, info.rid, &generics)?
    };

    // Register the type
    let TypeGenericsInfo {
        substs: _,
        region_params,
        region_params_map: _,
        type_params,
        type_params_map: _,
    } = generics;

    let name = type_def_id_to_name(tcx, info.rid);
    let region_params = ty::RegionVarId::Vector::from(region_params);
    let type_params = ty::TypeVarId::Vector::from(type_params);

    let type_def = ty::TypeDecl {
        def_id: trans_id,
        name,
        region_params: region_params,
        type_params: type_params,
        kind,
        // For now, initialize the regions hierarchy with a dummy value:
        // we compute it later (after returning to [translate_types]
        regions_hierarchy: regions_hierarchy::RegionGroups::new(),
    };

    trace!("{} -> {}", trans_id.to_string(), type_def.to_string());
    // Small sanity check - we have to translate the definitions in the proper
    // order, otherwise we mess up with the vector of ids
    assert!(type_defs.types.len() == trans_id.to_usize());

    type_defs.types.push_back(type_def);
    Ok(())
}

/// Translate the types.
///
/// Note that in practice, we don't really need to know in which order we should
/// extract them (i.e.: the `Declarations` parameter is not really
/// necessary), because what is important is the file generation later.
/// Still, now that the order is computed, it's better to use it (leads to a
/// better indexing, for instance).
pub fn translate_types(
    tcx: TyCtxt,
    decls: &OrderedDecls,
) -> Result<(TypesConstraintsMap, ty::TypeDecls)> {
    trace!();

    let mut types_cover_regions = TypesConstraintsMap::new();
    let mut type_defs = ty::TypeDecls::new();

    // Translate the types one by one
    for decl in &decls.decls {
        match decl {
            DeclarationGroup::Type(decl) => match decl {
                TypeDeclarationGroup::NonRec(id) => {
                    translate_type(tcx, decls, &mut type_defs, *id)?;
                    regions_hierarchy::compute_regions_hierarchy_for_type_decl_group(
                        &mut types_cover_regions,
                        &mut type_defs,
                        decl,
                    );
                }
                TypeDeclarationGroup::Rec(ids) => {
                    for id in ids {
                        translate_type(tcx, decls, &mut type_defs, *id)?;
                    }
                    regions_hierarchy::compute_regions_hierarchy_for_type_decl_group(
                        &mut types_cover_regions,
                        &mut type_defs,
                        decl,
                    );
                }
            },
            DeclarationGroup::Fun(_) | DeclarationGroup::Global(_) => {
                // Ignore the functions and constants
            }
        }
    }

    // Print the type constraints map
    trace!(
        "types constraints map:\n{}\n",
        regions_hierarchy::types_constraints_map_fmt_with_ctx(&types_cover_regions, &type_defs)
    );

    // Print the translated types
    let trans_ctx = TypeTransContext::new(&type_defs, &decls);
    for d in type_defs.types.iter() {
        trace!("translated type:\n{}\n", trans_ctx.format_object(d));
    }

    Ok((types_cover_regions, type_defs))
}
