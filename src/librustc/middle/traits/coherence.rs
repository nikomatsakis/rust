// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! See `doc.rs` for high-level documentation */

use super::{evaluate_impl, Overflow, DefinitelyApplicable,
            MaybeApplicable, NotApplicable};
use super::util;

use middle::subst;
use middle::subst::Subst;
use middle::ty;
use middle::typeck::infer::InferCtxt;
use syntax::ast;
use syntax::codemap::DUMMY_SP;
use util::ppaux::Repr;

pub fn impl_can_satisfy(infcx: &InferCtxt,
                        impl1_def_id: ast::DefId,
                        impl2_def_id: ast::DefId)
                        -> bool
{
    // `impl1` provides an implementation of `Foo<X,Y> for Z`.
    let impl1_substs =
        util::fresh_substs_for_impl(infcx, DUMMY_SP, impl1_def_id);
    let impl1_self_ty =
        ty::impl_trait_ref(infcx.tcx, impl1_def_id).unwrap()
            .self_ty()
            .subst(infcx.tcx, &impl1_substs);

    // Determine whether `impl2` can provide an implementation for those
    // same types.
    let param_env = ty::empty_parameter_environment();
    match evaluate_impl(infcx, &param_env, DUMMY_SP,
                        impl2_def_id, impl1_self_ty) {
        Overflow | DefinitelyApplicable | MaybeApplicable => true,
        NotApplicable => false,
    }
}

pub fn impl_is_local(tcx: &ty::ctxt,
                     impl_def_id: ast::DefId)
                     -> bool
{
    debug!("impl_is_local({})", impl_def_id.repr(tcx));
    match ty::impl_trait_ref(tcx, impl_def_id) {
        Some(trait_ref) => {
            debug!("trait_ref={}", trait_ref.repr(tcx));

            // If the trait is local to the crate, ok.
            if trait_ref.def_id.krate == ast::LOCAL_CRATE {
                debug!("trait {} is local to current crate",
                       trait_ref.def_id.repr(tcx));
                return true;
            }

            // Otherwise, self type must be local to the crate.
            let self_ty = ty::lookup_item_type(tcx, impl_def_id).ty;
            return ty_is_local(tcx, self_ty);
        }

        None => {
            // For inherent impls, self type must be a nominal type
            // defined in this crate.
            let self_ty = ty::lookup_item_type(tcx, impl_def_id).ty;
            match ty::get(self_ty).sty {
                ty::ty_enum(def_id, _) |
                ty::ty_struct(def_id, _) => {
                    debug!("inherent impl is defined on {} with def-id {}",
                           self_ty.repr(tcx),
                           def_id.repr(tcx));
                    def_id.krate == ast::LOCAL_CRATE
                }
                _ => {
                    false
                }
            }
        }
    }
}

pub fn ty_is_local(tcx: &ty::ctxt,
                   ty: ty::t)
                   -> bool
{
    debug!("ty_is_local({})", ty.repr(tcx));

    match ty::get(ty).sty {
        ty::ty_nil |
        ty::ty_bot |
        ty::ty_bool |
        ty::ty_char |
        ty::ty_int(..) |
        ty::ty_uint(..) |
        ty::ty_float(..) |
        ty::ty_str(..) => {
            false
        }

        ty::ty_bare_fn(..) |
        ty::ty_closure(..) => {
            false
        }

        ty::ty_vec(ty::mt { ty: t, .. }, _) |
        ty::ty_box(t) |
        ty::ty_uniq(t) |
        ty::ty_ptr(ty::mt { ty: t, .. }) |
        ty::ty_rptr(_, ty::mt { ty: t, .. }) => {
            ty_is_local(tcx, t)
        }

        ty::ty_tup(ref ts) => {
            ts.iter().any(|&t| ty_is_local(tcx, t))
        }

        ty::ty_enum(def_id, ref substs) |
        ty::ty_struct(def_id, ref substs) => {
            def_id.krate == ast::LOCAL_CRATE || {
                let variances = ty::item_variances(tcx, def_id);
                subst::ParamSpace::all().iter().any(|&space| {
                    substs.types.get_vec(space).iter().enumerate().any(
                        |(i, &t)| {
                            match *variances.types.get(space, i) {
                                ty::Bivariant => {
                                    // If Foo<T> is bivariant with respect to
                                    // T, then it doesn't matter whether T is
                                    // local or not, because `Foo<U>` for any
                                    // U will be a subtype of T.
                                    false
                                }
                                ty::Contravariant |
                                ty::Covariant |
                                ty::Invariant => {
                                    ty_is_local(tcx, t)
                                }
                            }
                        })
                })
            }
        }

        ty::ty_trait(ref tt) => {
            tt.def_id.krate == ast::LOCAL_CRATE
        }

        // Type parameters may be bound to types that are not local to
        // the crate.
        ty::ty_param(..) |
        ty::ty_infer(..) |
        ty::ty_err => {
            false
        }
    }
}
