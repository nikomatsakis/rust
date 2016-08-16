// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use check::regionck::RegionCtxt;

use hir::def_id::DefId;
use rustc::infer;
use middle::region;
use rustc::ty::subst;
use rustc::ty::{self, Ty, TyCtxt};
use util::nodemap::FnvHashSet;

use syntax::ast;
use syntax_pos::Span;

/// check_safety_of_destructor_if_necessary confirms that the type
/// expression `typ` conforms to the "Drop Check Rule" from the Sound
/// Generic Drop (RFC 769).
///
/// ----
///
/// The simplified (*) Drop Check Rule is the following:
///
/// Let `v` be some value (either temporary or named) and 'a be some
/// lifetime (scope). If the type of `v` owns data of type `D`, where
///
/// * (1.) `D` has a lifetime- or type-parametric Drop implementation,
///        (where that `Drop` implementation does not opt-out of
///         this check via the `unsafe_destructor_blind_to_params`
///         attribute), and
/// * (2.) the structure of `D` can reach a reference of type `&'a _`,
///
/// then 'a must strictly outlive the scope of v.
///
/// ----
///
/// This function is meant to by applied to the type for every
/// expression in the program.
///
/// ----
///
/// (*) The qualifier "simplified" is attached to the above
/// definition of the Drop Check Rule, because it is a simplification
/// of the original Drop Check rule, which attempted to prove that
/// some `Drop` implementations could not possibly access data even if
/// it was technically reachable, due to parametricity.
///
/// However, (1.) parametricity on its own turned out to be a
/// necessary but insufficient condition, and (2.)  future changes to
/// the language are expected to make it impossible to ensure that a
/// `Drop` implementation is actually parametric with respect to any
/// particular type parameter. (In particular, impl specialization is
/// expected to break the needed parametricity property beyond
/// repair.)
///
/// Therefore we have scaled back Drop-Check to a more conservative
/// rule that does not attempt to deduce whether a `Drop`
/// implementation could not possible access data of a given lifetime;
/// instead Drop-Check now simply assumes that if a destructor has
/// access (direct or indirect) to a lifetime parameter, then that
/// lifetime must be forced to outlive that destructor's dynamic
/// extent. We then provide the `unsafe_destructor_blind_to_params`
/// attribute as a way for destructor implementations to opt-out of
/// this conservative assumption (and thus assume the obligation of
/// ensuring that they do not access data nor invoke methods of
/// values that have been previously dropped).
///
pub fn check_safety_of_destructor_if_necessary<'a, 'gcx, 'tcx>(
    rcx: &mut RegionCtxt<'a, 'gcx, 'tcx>,
    typ: ty::Ty<'tcx>,
    span: Span,
    scope: region::CodeExtent)
{
    debug!("check_safety_of_destructor_if_necessary typ: {:?} scope: {:?}",
           typ, scope);

    let parent_scope = rcx.tcx.region_maps.opt_encl_scope(scope).unwrap_or_else(|| {
        span_bug!(span, "no enclosing scope found for scope: {:?}", scope)
    });

    let result = iterate_over_potentially_unsafe_regions_in_type(
        &mut DropckContext {
            rcx: rcx,
            span: span,
            parent_scope: parent_scope,
            breadcrumbs: FnvHashSet()
        },
        TypeContext::Root,
        typ,
        0);
    match result {
        Ok(()) => {}
        Err(Error::Overflow(ref ctxt, ref detected_on_typ)) => {
            let tcx = rcx.tcx;
            let mut err = struct_span_err!(tcx.sess, span, E0320,
                                           "overflow while adding drop-check rules for {}", typ);
            match *ctxt {
                TypeContext::Root => {
                    // no need for an additional note if the overflow
                    // was somehow on the root.
                }
                TypeContext::ADT { def_id, variant, field } => {
                    let adt = tcx.lookup_adt_def(def_id);
                    let variant_name = match adt.adt_kind() {
                        ty::AdtKind::Enum => format!("enum {} variant {}",
                                                     tcx.item_path_str(def_id),
                                                     variant),
                        ty::AdtKind::Struct => format!("struct {}",
                                                       tcx.item_path_str(def_id))
                    };
                    span_note!(
                        &mut err,
                        span,
                        "overflowed on {} field {} type: {}",
                        variant_name,
                        field,
                        detected_on_typ);
                }
            }
            err.emit();
        }
    }
}

enum Error<'tcx> {
    Overflow(TypeContext, ty::Ty<'tcx>),
}

#[derive(Copy, Clone)]
enum TypeContext {
    Root,
    ADT {
        def_id: DefId,
        variant: ast::Name,
        field: ast::Name,
    }
}

struct DropckContext<'a, 'b: 'a, 'gcx: 'b+'tcx, 'tcx: 'b> {
    rcx: &'a mut RegionCtxt<'b, 'gcx, 'tcx>,
    /// types that have already been traversed
    breadcrumbs: FnvHashSet<Ty<'tcx>>,
    /// span for error reporting
    span: Span,
    /// the scope reachable dtorck types must outlive
    parent_scope: region::CodeExtent
}

// `context` is used for reporting overflow errors
fn iterate_over_potentially_unsafe_regions_in_type<'a, 'b, 'gcx, 'tcx>(
    cx: &mut DropckContext<'a, 'b, 'gcx, 'tcx>,
    context: TypeContext,
    ty: Ty<'tcx>,
    depth: usize) -> Result<(), Error<'tcx>>
{
    let tcx = cx.rcx.tcx;
    // Issue #22443: Watch out for overflow. While we are careful to
    // handle regular types properly, non-regular ones cause problems.
    let recursion_limit = tcx.sess.recursion_limit.get();
    if depth / 4 >= recursion_limit {
        // This can get into rather deep recursion, especially in the
        // presence of things like Vec<T> -> Unique<T> -> PhantomData<T> -> T.
        // use a higher recursion limit to avoid errors.
        return Err(Error::Overflow(context, ty))
    }

    // canoncialize the regions in `ty` before inserting - infinitely many
    // region variables can refer to the same region.
    let ty = cx.rcx.resolve_type_and_region_vars_if_possible(&ty);

    if !cx.breadcrumbs.insert(ty) {
        debug!("iterate_over_potentially_unsafe_regions_in_type \
               {}ty: {} scope: {:?} - cached",
               (0..depth).map(|_| ' ').collect::<String>(),
               ty, cx.parent_scope);
        return Ok(()); // we already visited this type
    }
    debug!("iterate_over_potentially_unsafe_regions_in_type \
           {}ty: {} scope: {:?}",
           (0..depth).map(|_| ' ').collect::<String>(),
           ty, cx.parent_scope);

    // If `typ` has a destructor, then we must ensure that all
    // borrowed data reachable via `typ` must outlive the parent
    // of `scope`. This is handled below.
    //
    // However, there is an important special case: for any Drop
    // impl that is tagged as "blind" to their parameters,
    // we assume that data borrowed via such type parameters
    // remains unreachable via that Drop impl.
    //
    // For example, consider:
    //
    // ```rust
    // #[unsafe_destructor_blind_to_params]
    // impl<T> Drop for Vec<T> { ... }
    // ```
    //
    // which does have to be able to drop instances of `T`, but
    // otherwise cannot read data from `T`.
    //
    // Of course, for the type expression passed in for any such
    // unbounded type parameter `T`, we must resume the recursive
    // analysis on `T` (since it would be ignored by
    // type_must_outlive).
    if has_dtor_of_interest(tcx, ty) {
        debug!("iterate_over_potentially_unsafe_regions_in_type \
                {}ty: {} - is a dtorck type!",
               (0..depth).map(|_| ' ').collect::<String>(),
               ty);

        cx.rcx.type_must_outlive(infer::SubregionOrigin::SafeDestructor(cx.span),
                                 ty, ty::ReScope(cx.parent_scope));

        return Ok(());
    }

    debug!("iterate_over_potentially_unsafe_regions_in_type \
           {}ty: {} scope: {:?} - checking interior",
           (0..depth).map(|_| ' ').collect::<String>(),
           ty, cx.parent_scope);

    // We still need to ensure all referenced data is safe.
    match ty.sty {
        ty::TyBool | ty::TyChar | ty::TyInt(_) | ty::TyUint(_) |
        ty::TyFloat(_) | ty::TyStr => {
            // primitive - definitely safe
            Ok(())
        }

        ty::TyBox(ity) | ty::TyArray(ity, _) | ty::TySlice(ity) => {
            // single-element containers, behave like their element
            iterate_over_potentially_unsafe_regions_in_type(
                cx, context, ity, depth+1)
        }

        ty::TyStruct(def, substs) if def.is_phantom_data() => {
            // PhantomData<T> - behaves identically to T
            let ity = *substs.types.get(subst::TypeSpace, 0);
            iterate_over_potentially_unsafe_regions_in_type(
                cx, context, ity, depth+1)
        }

        ty::TyStruct(def, substs) | ty::TyEnum(def, substs) => {
            let did = def.did;
            for variant in &def.variants {
                for field in variant.fields.iter() {
                    let fty = field.ty(tcx, substs);
                    let fty = cx.rcx.fcx.resolve_type_vars_with_obligations(
                        cx.rcx.fcx.normalize_associated_types_in(cx.span, &fty));
                    iterate_over_potentially_unsafe_regions_in_type(
                        cx,
                        TypeContext::ADT {
                            def_id: did,
                            field: field.name,
                            variant: variant.name,
                        },
                        fty,
                        depth+1)?
                }
            }
            Ok(())
        }

        ty::TyTuple(tys) |
        ty::TyClosure(_, ty::ClosureSubsts { upvar_tys: tys, .. }) => {
            for ty in tys {
                iterate_over_potentially_unsafe_regions_in_type(cx, context, ty, depth+1)?
            }
            Ok(())
        }

        ty::TyRawPtr(..) | ty::TyRef(..) | ty::TyParam(..) => {
            // these always come with a witness of liveness (references
            // explicitly, pointers implicitly, parameters by the
            // caller).
            Ok(())
        }

        ty::TyFnDef(..) | ty::TyFnPtr(_) => {
            // FIXME(#26656): this type is always destruction-safe, but
            // it implicitly witnesses Self: Fn, which can be false.
            Ok(())
        }

        ty::TyInfer(..) | ty::TyError => {
            tcx.sess.delay_span_bug(cx.span, "unresolved type in regionck");
            Ok(())
        }

        // these are always dtorck
        ty::TyTrait(..) | ty::TyProjection(_) => bug!(),
    }
}

fn has_dtor_of_interest<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>,
                                        ty: Ty<'tcx>) -> bool {
    match ty.sty {
        ty::TyEnum(def, _) | ty::TyStruct(def, _) => {
            def.is_dtorck(tcx)
        }
        ty::TyTrait(..) | ty::TyProjection(..) => {
            debug!("ty: {:?} isn't known, and therefore is a dropck type", ty);
            true
        },
        _ => false
    }
}
