// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::subst::{SelfSpace, Subst, VecPerParamSpace};
use middle::traits::{Obligation, VtableOrigin,
                     ResolvedTo, ResolvedToUnimpl, ResolvedToOverflow,
                     Vtable, VtableImpl, VtableUnboxedClosure,
                     VtableParam, Builtin, Resolution,
                     obligations_for_generics, try_resolve_obligation};
use middle::ty;
use middle::typeck::{CrateCtxt, MethodCall};
use middle::typeck::check::{blank_fn_ctxt,
                            FnCtxt,
                            Inherited,
                            PendingObligation,
                            structurally_resolved_type,
                            writeback};
use middle::typeck::infer;
use std::rc::Rc;
use syntax::ast;
use syntax::ast_util;
use util::ppaux::UserString;
use util::ppaux::Repr;
use util::common::unstable_partition;

pub fn resolve_impl(ccx: &CrateCtxt,
                    impl_item: &ast::Item,
                    impl_polyty: &ty::Polytype,
                    impl_trait_ref: &ty::TraitRef)
{
    /*!
     * The situation is as follows. We have some trait like:
     *
     *    trait Foo<A:Clone> : Bar {
     *        fn method() { ... }
     *    }
     *
     * and an impl like:
     *
     *    impl<B:Clone> Foo<B> for int { ... }
     *
     * We want to validate that the various requirements of the trait
     * are met:
     *
     *    A:Clone, Self:Bar
     *
     * But of course after substituting the types from the impl
     * (A => B, Self => int):
     *
     *    B:Clone, int:Bar
     *
     * We store these results away as the "impl_res" for use by the
     * default methods.
     */

    debug!("resolve_impl(impl_item.id={})",
           impl_item.id);

    let tcx = ccx.tcx;
    let param_env = ty::construct_parameter_environment(tcx,
                                                        impl_item.span,
                                                        &impl_polyty.generics,
                                                        impl_item.id);
    let inh = &Inherited::new(tcx, param_env);
    let fcx = &blank_fn_ctxt(ccx, inh, ty::mk_err(), impl_item.id);

    // The impl_trait_ref in our example above would be
    //     `Foo<B> for int`
    let impl_trait_ref = impl_trait_ref.subst(tcx, &inh.param_env.free_substs);
    debug!("impl_trait_ref={}", impl_trait_ref.repr(tcx));

    // Resolve the vtables for the trait reference on the impl.  This
    // serves many purposes, best explained by example. Imagine we have:
    //
    //    trait A<T:B> : C { fn x(&self) { ... } }
    //
    // and
    //
    //    impl A<int> for uint { ... }
    //
    // In that case, the trait ref will be `A<int> for uint`. Resolving
    // this will first check that the various types meet their requirements:
    //
    // 1. Because of T:B, int must implement the trait B
    // 2. Because of the supertrait C, uint must implement the trait C.
    //
    // Simultaneously, the result of this resolution (`vtbls`), is precisely
    // the set of vtable information needed to compile the default method
    // `x()` adapted to the impl. (After all, a default method is basically
    // the same as:
    //
    //     fn default_x<T:B, Self:A>(...) { .. .})

    let trait_def = ty::lookup_trait_def(tcx, impl_trait_ref.def_id);
    let obligations = obligations_for_generics(tcx,
                                               impl_item.span,
                                               &trait_def.generics,
                                               &impl_trait_ref.substs);
    let opt_resolutions =
        obligations.map(
            |obligation| try_resolve_obligation(fcx.infcx(),
                                                &fcx.inh.param_env,
                                                obligation));

    debug!("opt_resolutions for impl {} are {}",
           impl_item.id,
           opt_resolutions.repr(tcx));

    fcx.infcx().resolve_regions_and_report_errors();
    for (space, i, resolution) in opt_resolutions.enumerated_iter() {
        let obligation = obligations.get(space, i);
        check_obligation_for_error(fcx, obligation, resolution.as_ref());
    }

    let all_success = opt_resolutions.all(|r| {
        match *r {
            Some(ResolvedTo(_)) => true,
            _ => false
        }
    });

    if all_success {
        let resolutions = opt_resolutions.map_move(|opt_resolution| {
            match opt_resolution {
                Some(ResolvedTo(origin)) => origin,
                _ => fail!("Only expected success")
            }
        });
        let resolutions =
            writeback::resolve_impl_res(fcx.infcx(),
                                        impl_item.span,
                                        &resolutions);
        let impl_def_id = ast_util::local_def(impl_item.id);
        tcx.impl_vtables.borrow_mut().insert(impl_def_id, Rc::new(resolutions));
    }
}

pub fn check_object_cast(fcx: &FnCtxt,
                         cast_expr: &ast::Expr,
                         source_expr: &ast::Expr,
                         target_object_ty: ty::t)
{
    // Look up vtables for the type we're casting to,
    // passing in the source and target type.  The source
    // must be a pointer type suitable to the object sigil,
    // e.g.: `&x as &Trait` or `box x as Box<Trait>`
    let source_ty = fcx.expr_ty(source_expr);
    let source_ty = structurally_resolved_type(fcx, source_expr.span, source_ty);
    match (&ty::get(source_ty).sty, &ty::get(target_object_ty).sty) {
        (&ty::ty_uniq(referent_ty), &ty::ty_uniq(ref target_trait_ty)) => {
            let target_trait = target_trait(target_trait_ty);
            // Ensure that if ~T is cast to ~Trait, then T : Trait
            push_cast_obligation(fcx, cast_expr, target_trait, referent_ty);
        }

        (&ty::ty_rptr(referent_region, ty::mt { ty: referent_ty,
                                                mutbl: referent_mutbl }),
         &ty::ty_rptr(target_region, ty::mt { ty: ref target_trait_ty,
                                              mutbl: target_mutbl })) =>
        {
            let target_trait = target_trait(target_trait_ty);
            if !mutability_allowed(referent_mutbl, target_mutbl) {
                fcx.tcx().sess.span_err(source_expr.span,
                                        "types differ in mutability");
            } else {
                // Ensure that if &'a T is cast to &'b Trait, then T : Trait
                push_cast_obligation(fcx, cast_expr, target_trait, referent_ty);

                // Ensure that if &'a T is cast to &'b Trait, then 'b <= 'a
                infer::mk_subr(fcx.infcx(), false,
                               infer::RelateObjectBound(source_expr.span),
                               target_region, referent_region);
            }
        }

        (_, &ty::ty_uniq(..)) => {
            fcx.ccx.tcx.sess.span_err(
                source_expr.span,
                format!("can only cast an boxed pointer \
                         to a boxed object, not a {}",
                        ty::ty_sort_string(fcx.tcx(), source_ty)).as_slice());
        }

        (_, &ty::ty_rptr(..)) => {
            fcx.ccx.tcx.sess.span_err(
                source_expr.span,
                format!("can only cast a &-pointer \
                         to an &-object, not a {}",
                        ty::ty_sort_string(fcx.tcx(), source_ty)).as_slice());
        }

        _ => {
            fcx.tcx().sess.span_bug(
                source_expr.span,
                "expected object type");
        }
    }

    // Because we currently give unsound lifetimes to the "ty_box", I
    // could have written &'static ty::TyTrait here, but it seems
    // gratuitously unsafe.
    fn target_trait<'a>(t: &'a ty::t) -> &'a ty::TyTrait {
        match ty::get(*t).sty {
            ty::ty_trait(ref ty_trait) => &**ty_trait,
            _ => fail!("expected ty_trait")
        }
    }

    fn mutability_allowed(a_mutbl: ast::Mutability,
                          b_mutbl: ast::Mutability)
                          -> bool {
        a_mutbl == b_mutbl ||
            (a_mutbl == ast::MutMutable && b_mutbl == ast::MutImmutable)
    }

    fn push_cast_obligation(fcx: &FnCtxt,
                            cast_expr: &ast::Expr,
                            target_trait: &ty::TyTrait,
                            referent_ty: ty::t) {
        // Take the type parameters from the object type, but set
        // the Self type (which is unknown, for the object type)
        // to be the type we are casting from.
        let mut target_substs = target_trait.substs.clone();
        assert!(target_substs.self_ty().is_none());
        target_substs.types.push(SelfSpace, referent_ty);

        // Create the obligation for casting from T to Trait.
        let target_trait_ref =
            Rc::new(ty::TraitRef { def_id: target_trait.def_id,
                                   substs: target_substs });
        let target_obligation = Obligation::new(cast_expr.span,
                                                target_trait_ref);
        let pending_resolution = fcx.add_obligation(target_obligation);

        let mut r = VecPerParamSpace::empty();
        r.push(SelfSpace, pending_resolution);
        fcx.write_vtables(MethodCall::expr(cast_expr.id), r);
    }
}

pub fn resolve_fcx_obligations_or_error(fcx: &FnCtxt) {
    debug!("resolve_fcx_obligations_or_error");
    try_resolve_fcx_obligations(fcx);

    for pending_obligation in fcx.inh.obligations.borrow().iter() {
        check_obligation_for_error(fcx,
                                   &pending_obligation.obligation,
                                   pending_obligation.resolution.get());
    }
}

fn resolve_trait_ref(fcx: &FnCtxt, obligation: &Obligation)
                     -> (ty::TraitRef, ty::t)
{
    let trait_ref =
        fcx.infcx().resolve_type_vars_in_trait_ref_if_possible(
            &*obligation.trait_ref);
    let self_ty =
        trait_ref.substs.self_ty().unwrap();
    (trait_ref, self_ty)
}

fn check_obligation_for_error(fcx: &FnCtxt,
                              obligation: &Obligation,
                              resolution: Option<&Resolution<VtableOrigin>>) {
    match resolution {
        Some(&ResolvedTo(ref origin)) => {
            // Found an impl. Still, it is possible that this
            // resolution triggered deferred type errors.
            check_vtable_origin_for_error(fcx, obligation, origin);
        }

        Some(&ResolvedToUnimpl) => {
            // No impl exists.
            let (trait_ref, self_ty) = resolve_trait_ref(fcx, obligation);
            fcx.tcx().sess.span_err(
                obligation.span,
                format!(
                    "could not locate an impl of the trait `{}` for \
                     the type `{}`",
                    trait_ref.user_string(fcx.tcx()),
                    self_ty.user_string(fcx.tcx())).as_slice());
        }

        Some(&ResolvedToOverflow) => {
            // Overflow during resolution; cycle.
            report_overflow(fcx, obligation);
        }

        None => {
            maybe_report_ambiguity(fcx, obligation);
        }
    }
}

pub fn report_overflow(fcx: &FnCtxt, obligation: &Obligation) {
    let (trait_ref, self_ty) = resolve_trait_ref(fcx, obligation);
    fcx.tcx().sess.span_err(
        obligation.span,
        format!(
            "could not locate an impl of the trait `{}` for \
             the type `{}` due to overflow; possible cyclic \
             dependency between impls",
            trait_ref.user_string(fcx.tcx()),
            self_ty.user_string(fcx.tcx())).as_slice());
}

pub fn maybe_report_ambiguity(fcx: &FnCtxt, obligation: &Obligation) {
    // Unable to successfully determine, probably means
    // insufficient type information, but could mean
    // ambiguous impls. The latter *ought* to be a
    // coherence violation, so we don't report it here.
    let (trait_ref, self_ty) = resolve_trait_ref(fcx, obligation);
    debug!("maybe_report_ambiguity(trait_ref={}, self_ty={}, obligation={})",
           trait_ref.repr(fcx.tcx()),
           self_ty.repr(fcx.tcx()),
           obligation.repr(fcx.tcx()));
    if ty::type_needs_infer(self_ty) {
        fcx.tcx().sess.span_err(
            obligation.span,
            format!(
                "unable to infer enough type information to \
             locate the impl of the trait `{}` for \
             the type `{}`; type annotations required",
            trait_ref.user_string(fcx.tcx()),
            self_ty.user_string(fcx.tcx())).as_slice());
    } else {
         // Ambiguity. Coherence should have reported an error.
        assert!(fcx.tcx().sess.err_count() > 0);
    }
}

pub fn check_vtable_origin_for_error(fcx: &FnCtxt,
                                     obligation: &Obligation,
                                     origin: &VtableOrigin)
{
    match *origin {
        Vtable(_, Some(ref err)) |
        VtableParam(_, Some(ref err)) => {
            let trait_ref =
                fcx.infcx().resolve_type_vars_in_trait_ref_if_possible(
                    &*obligation.trait_ref);

            // Don't report derived errors.
            if trait_ref.substs.types.any(|&t| ty::type_is_error(t)) {
                return;
            }

            let self_ty = trait_ref.substs.self_ty().unwrap();
            let msg = ty::type_err_to_str(fcx.tcx(), err);
            let msg = format!("mismatched types matching `{}` against `{}`: {}",
                              trait_ref.user_string(fcx.tcx()),
                              self_ty.user_string(fcx.tcx()),
                              msg);
            fcx.tcx().sess.span_err(obligation.span, msg.as_slice());
            ty::note_and_explain_type_err(fcx.tcx(), err);
        }

        Vtable(VtableImpl(ref vtable), None) => {
            for r in vtable.origins.iter() {
                check_vtable_origin_for_error(fcx, obligation, r);
            }
        }

        Vtable(VtableUnboxedClosure(..), None) => {
        }

        VtableParam(_, None) => {
        }

        Builtin => { }
    }
}

pub fn try_resolve_fcx_obligations(fcx: &FnCtxt) -> bool {
    /*!
     * Iterate over any pending obligations that have not yet been
     * resolved and try to resolve them. Repeats so long as progress
     * is being made (so there is no point in calling twice in a
     * row). Returns true if anything was successfully resolved, or
     * false otherwise. A true result indicates that more type
     * information *may* be available.
     */

    let mut obligations = fcx.inh.obligations.borrow_mut();
    let original_resolved = fcx.inh.resolved_obligations_count.get();

    debug!("try_resolve_fcx_obligations({}/{} resolved) start",
           original_resolved, obligations.len());

    // Invariant: indices in range {0 <= _ < resolved} are resolved.
    let mut resolved = original_resolved;

    loop {
        // all resolutions not yet fulfilled
        let pending_obligations: &mut [PendingObligation] =
            obligations.mut_slice_from(resolved);

        // try to fulfill obligations and partition those that are
        // not yet resolved to the back
        let newly_resolved =
            unstable_partition(pending_obligations,
                               |p_o| !try_resolve_pending_obligation(fcx, p_o));

        // increment total number of resolved obligations. break if no progress.
        if newly_resolved == 0 {
            break;
        }
        resolved += newly_resolved;
    }

    debug!("try_resolve_fcx_obligations({}/{} resolved) end",
           resolved, obligations.len());

    fcx.inh.resolved_obligations_count.set(resolved);
    return resolved != original_resolved;

    fn try_resolve_pending_obligation(fcx: &FnCtxt,
                                      pending_obligation: &PendingObligation)
                                      -> bool
    {
        /*!
         * Try to fulfill the obligation. Return true if we are succesful.
         */

        let &PendingObligation {
            obligation: ref o,
            resolution: ref pending_resolution
        } = pending_obligation;

        match try_resolve_obligation(fcx.infcx(), &fcx.inh.param_env, o) {
            Some(resolution) => {
                debug!("obligation {} resolved to: {}",
                       o.repr(fcx.tcx()), resolution.repr(fcx.tcx()));
                pending_resolution.fulfill(resolution).unwrap();
                true
            }
            None => {
                debug!("obligation not yet resolved");
                false
            }
        }
    }
}
