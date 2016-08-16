// Copyright 2014-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Special rules applies to impls of particular traits.

use CrateCtxt;

use hir::def_id::DefId;
use middle::free_region::FreeRegionMap;
use rustc::dep_graph::DepNode;
use rustc::infer;
use rustc::ty::{self, Ty, TyCtxt};
use rustc::ty::subst::{self, Subst};
use rustc::ty::wf;
use rustc::traits::{self, ProjectionMode};
use rustc_data_structures::fnv::FnvHashSet;

use syntax_pos;

pub fn check_all_special_trait_impls(ccx: &CrateCtxt) {
    let _task = ccx.tcx.dep_graph.in_task(DepNode::Dropck);

    if let Some(id) = ccx.tcx.lang_items.drop_trait() {
        check_special_trait_impls(ccx, id, SpecialTrait::Drop);
    }

    if let Some(id) = ccx.tcx.lang_items.copy_trait() {
        check_special_trait_impls(ccx, id, SpecialTrait::Copy);
    }
}

fn check_special_trait_impls(ccx: &CrateCtxt, trait_def_id: DefId, special: SpecialTrait) {
    let trait_def = ccx.tcx.lookup_trait_def(trait_def_id);
    trait_def.for_each_impl(ccx.tcx, |impl_did| {
        let _task = ccx.tcx.dep_graph.in_task(DepNode::DropckImpl(impl_did)); // TODO
        if impl_did.is_local() {
            match check_special_impl(ccx, impl_did, special) {
                Ok(()) => {}
                Err(()) => {
                    assert!(ccx.tcx.sess.has_errors());
                }
            }
        }
    });
}

/// check_drop_impl confirms that the Drop implementation identfied by
/// `drop_impl_did` is not any more specialized than the type it is
/// attached to (Issue #8142).
///
/// This means:
///
/// 1. The self type must be nominal (this is already checked during
///    coherence),
///
/// 2. The generic region/type parameters of the impl's self-type must
///    all be parameters of the Drop impl itself (i.e. no
///    specialization like `impl Drop for Foo<i32>`), and,
///
/// 3. Any bounds on the generic parameters must be reflected in the
///    struct/enum definition for the nominal type itself (i.e.
///    cannot do `struct S<T>; impl<T:Clone> Drop for S<T> { ... }`).
///
fn check_special_impl(ccx: &CrateCtxt, special_impl_did: DefId, special: SpecialTrait) -> Result<(), ()> {
    assert!(special_impl_did.is_local());
    let ty::TypeScheme { generics: ref dtor_generics,
                         ty: dtor_self_type } = ccx.tcx.lookup_item_type(special_impl_did);
    let dtor_predicates = ccx.tcx.lookup_predicates(special_impl_did);
    match dtor_self_type.sty {
        ty::TyEnum(adt_def, self_to_impl_substs) |
        ty::TyStruct(adt_def, self_to_impl_substs) => {
            ensure_special_params_and_item_params_correspond(ccx.tcx,
                                                             special_impl_did,
                                                             dtor_generics,
                                                             &dtor_self_type,
                                                             adt_def.did,
                                                             special)?;

            ensure_special_predicates_are_implied_by_item_defn(ccx.tcx,
                                                               special_impl_did,
                                                               &dtor_predicates,
                                                               dtor_self_type,
                                                               adt_def.did,
                                                               self_to_impl_substs,
                                                               special)
        }
        _ => {
            // Destructors only work on nominal types.  This was
            // already checked by coherence, so we can panic here.
            let span = ccx.tcx.map.def_id_span(special_impl_did, syntax_pos::DUMMY_SP);
            span_bug!(span,
                      "should have been rejected by coherence check: {}",
                      dtor_self_type);
        }
    }
}

fn ensure_special_params_and_item_params_correspond<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    special_impl_did: DefId,
    special_impl_generics: &ty::Generics<'tcx>,
    special_impl_ty: &ty::Ty<'tcx>,
    self_type_did: DefId,
    special: SpecialTrait)
    -> Result<(), ()>
{
    let special_impl_node_id = tcx.map.as_local_node_id(special_impl_did).unwrap();
    let self_type_node_id = tcx.map.as_local_node_id(self_type_did).unwrap();

    // check that the impl type can be made to match the trait type.

    let impl_param_env = ty::ParameterEnvironment::for_item(tcx, self_type_node_id);
    tcx.infer_ctxt(None, Some(impl_param_env), ProjectionMode::AnyFinal).enter(|infcx| {
        let tcx = infcx.tcx;
        let mut fulfillment_cx = traits::FulfillmentContext::new();

        let named_type = tcx.lookup_item_type(self_type_did).ty;
        let named_type = named_type.subst(tcx, &infcx.parameter_environment.free_substs);

        let special_impl_span = tcx.map.def_id_span(special_impl_did, syntax_pos::DUMMY_SP);
        let fresh_impl_substs =
            infcx.fresh_substs_for_generics(special_impl_span, special_impl_generics);
        let fresh_impl_self_ty = special_impl_ty.subst(tcx, &fresh_impl_substs);

        if let Err(_) = infcx.eq_types(true, infer::TypeOrigin::Misc(special_impl_span),
                                       named_type, fresh_impl_self_ty) {
            let item_span = tcx.map.span(self_type_node_id);
            struct_span_err!(tcx.sess, special_impl_span, E0366,
                             "implementations of `{:?}` cannot be specialized",
                             special)
                .span_note(item_span,
                           "use same sequence of generic type and region \
                            parameters that is on the struct/enum definition")
                .emit();
            return Err(());
        }

        if let Err(ref errors) = fulfillment_cx.select_all_or_error(&infcx) {
            // this could be reached when we get lazy normalization
            infcx.report_fulfillment_errors(errors);
            return Err(());
        }

        if let Err(ref errors) = fulfillment_cx.select_rfc1592_obligations(&infcx) {
            infcx.report_fulfillment_errors_as_warnings(errors, special_impl_node_id);
        }

        let free_regions = FreeRegionMap::new();
        infcx.resolve_regions_and_report_errors(&free_regions, special_impl_node_id);
        Ok(())
    })
}

/// Confirms that every predicate imposed by dtor_predicates is
/// implied by assuming the predicates attached to self_type_did.
fn ensure_special_predicates_are_implied_by_item_defn<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    special_impl_did: DefId,
    dtor_predicates: &ty::GenericPredicates<'tcx>,
    self_type: Ty<'tcx>,
    self_type_did: DefId,
    _self_to_impl_substs: &subst::Substs<'tcx>,
    special: SpecialTrait)
    -> Result<(), ()>
{
    // Here is an example, analogous to that from
    // `compare_impl_method`.
    //
    // Consider a struct type:
    //
    //     struct Type<'c, 'b:'c, 'a> {
    //         x: &'a Contents            // (contents are irrelevant;
    //         y: &'c Cell<&'b Contents>, //  only the bounds matter for our purposes.)
    //     }
    //
    // and a Drop impl:
    //
    //     impl<'z, 'y:'z, 'x:'y> Drop for P<'z, 'y, 'x> {
    //         fn drop(&mut self) { self.y.set(self.x); } // (only legal if 'x: 'y)
    //     }
    //
    // We start out with self_to_impl_substs, that maps the generic
    // parameters of Type to that of the Drop impl.
    //
    //     self_to_impl_substs = {'c => 'z, 'b => 'y, 'a => 'x}
    //
    // Applying this to the predicates (i.e. assumptions) provided by the item
    // definition yields the instantiated assumptions:
    //
    //     ['y : 'z]
    //
    // We then check all of the predicates of the Drop impl:
    //
    //     ['y:'z, 'x:'y]
    //
    // and ensure each is in the list of instantiated
    // assumptions. Here, `'y:'z` is present, but `'x:'y` is
    // absent. So we report an error that the Drop impl injected a
    // predicate that is not present on the struct definition.

    let special_impl_node_id = tcx.map.as_local_node_id(special_impl_did).unwrap();
    let impl_param_env = ty::ParameterEnvironment::for_item(tcx, special_impl_node_id);
    tcx.infer_ctxt(None, Some(impl_param_env), ProjectionMode::AnyFinal).enter(|infcx| {
        // Find the conditions that make the self-type well-formed.
        let special_impl_span = tcx.map.span(special_impl_node_id);
        let assumptions_in_impl_context: FnvHashSet<_> =
            wf::obligations(&infcx,
                            special_impl_node_id,
                            self_type,
                            special_impl_span)
            .unwrap_or(vec![])
            .into_iter()
            .map(|obligation| obligation.predicate)
            .collect();

        // An earlier version of this code attempted to do this checking
        // via the traits::fulfill machinery. However, it ran into trouble
        // since the fulfill machinery merely turns outlives-predicates
        // 'a:'b and T:'b into region inference constraints. It is simpler
        // just to look for all the predicates directly.

        assert!(dtor_predicates.predicates.is_empty_in(subst::SelfSpace));
        assert!(dtor_predicates.predicates.is_empty_in(subst::FnSpace));
        let predicates = dtor_predicates.predicates.get_slice(subst::TypeSpace);
        for predicate in predicates {
            // (We do not need to worry about deep analysis of type
            // expressions etc because the Drop impls are already forced
            // to take on a structure that is roughly an alpha-renaming of
            // the generic parameters of the item definition.)

            // This path now just checks *all* predicates via the direct
            // lookup, rather than using fulfill machinery.
            //
            // However, it may be more efficient in the future to batch
            // the analysis together via the fulfill , rather than the
            // repeated `contains` calls.

            match special {
                SpecialTrait::Drop => {
                    // Drop impls cannot have any requirements beyond
                    // those specified on the type itself. This is because
                    // we want a drop impl to either *always* or *never*
                    // apply to a given type.
                }
                SpecialTrait::Copy => {
                    // It is ok for Copy impls to require that types are `Copy`,
                    // but not for them to add arbitrary other predicates.
                    //
                    // This is because we want to be able to test whether `T: Copy`
                    // holds without that requiring new obligations to be proven,
                    // and *in particular* not region obligations. Ignoring those obligations
                    // (as in #29149) would be unsound in a way, but requiring them to
                    // hold would be unfair, because maybe the program uses the value
                    // in an affine way.
                    //
                    // This is related to the lifetime dispatch question
                    // of specialization, and it may indeed (as described
                    // in #29149) make sense to eventually generalize this
                    // check to employ that same machinery.
                    let copy_def_id = tcx.lang_items.copy_trait().unwrap();
                    if let Some(trait_ref) = predicate.to_opt_poly_trait_ref() {
                        if trait_ref.def_id() == copy_def_id {
                            continue;
                        }
                    }
                }
            }

            if !assumptions_in_impl_context.contains(&predicate) {
                let type_span = tcx.map.span_if_local(self_type_did).unwrap();
                struct_span_err!(tcx.sess, special_impl_span, E0367,
                                 "the requirement `{}` is added only by the `{:?}` impl.",
                                 predicate,
                                 special)
                    .span_note(type_span,
                               "the same requirement must be part of \
                                the struct/enum definition")
                .emit();
            }
        }

        if tcx.sess.has_errors() {
            return Err(());
        }
        Ok(())
    })
}

#[derive(Copy, Clone, Debug)]
enum SpecialTrait {
    Drop,
    Copy,
}
