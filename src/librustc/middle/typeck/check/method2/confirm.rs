// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use super::Ambiguity;
use super::CandidateSource;
use super::ImplSource;
use super::MethodError;
use super::MethodIndex;
use super::NoMatch;
use super::TraitSource;
use super::probe;

use middle::subst;
use middle::subst::Subst;
use middle::traits;
use middle::ty;
use middle::ty_fold::TypeFoldable;
use middle::typeck::check;
use middle::typeck::check::{FnCtxt, NoPreference};
use middle::typeck::check::regionmanip::replace_late_bound_regions;
use middle::typeck::{MethodCallee, MethodObject, MethodOrigin,
                     MethodParam, MethodStatic, MethodTraitObject, MethodTypeParam};
use middle::typeck::infer;
use middle::typeck::infer::InferCtxt;
use syntax::ast;
use syntax::codemap::Span;
use std::collections::HashSet;
use std::rc::Rc;
use std::mem;
use util::ppaux::Repr;

pub struct ConfirmContext<'a, 'tcx:'a> {
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    self_expr_id: ast::NodeId,
}

impl<'a,'tcx> ConfirmContext<'a,'tcx> {
    pub fn new(fcx: &'a FnCtxt<'a, 'tcx>,
               span: Span,
               self_expr_id: ast::NodeId)
               -> ConfirmContext<'a, 'tcx>
    {
        ConfirmContext { fcx: fcx, span: span, self_expr_id: self_expr_id }
    }

    pub fn confirm(&mut self,
                   self_ty: ty::t,
                   pick: probe::Pick,
                   supplied_method_types: Vec<ty::t>)
                   -> MethodCallee
    {
        //
        let self_ty = self.adjust_self_ty(self_ty, &pick.adjustment);

        //
        self.enforce_drop_trait_limitations(&pick);

        //
        let (rcvr_substs, method_origin) =
            self.fresh_receiver_substs(self_ty, &pick);
        let (method_types, method_regions) =
            self.instantiate_method_substs(&pick, supplied_method_types);
        let all_substs = rcvr_substs.with_method(method_types, method_regions);

        //
        let method_sig = self.instantiate_method_sig(&pick, &all_substs);
        let method_self_ty = method_sig.inputs[0];

        //
        self.unify_receivers(self_ty, method_self_ty);

        //
        self.add_obligations(&pick, &all_substs);

        //
        let fty = ty::mk_bare_fn(self.tcx(), ty::BareFnTy {
            sig: method_sig,
            fn_style: pick.method_ty.fty.fn_style,
            abi: pick.method_ty.fty.abi.clone(),
        });

        MethodCallee {
            origin: method_origin,
            ty: fty,
            substs: all_substs
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // ADJUSTMENTS

    fn adjust_self_ty(&mut self,
                      self_ty: ty::t,
                      adjustment: &probe::PickAdjustment)
                      -> ty::t
    {
        let adjustment = ty::AdjustDerefRef(self.create_ty_adjustment(adjustment));
        let adjusted_ty =
            ty::adjust_ty(
                self.tcx(), self.span, self.self_expr_id, self_ty, Some(&adjustment),
                |method_call| self.fcx.inh.method_map.borrow()
                                                     .find(&method_call)
                                                     .map(|method| method.ty));
        self.fcx.write_adjustment(self.self_expr_id, self.span, adjustment);
        adjusted_ty
    }

    fn create_ty_adjustment(&mut self,
                            adjustment: &probe::PickAdjustment)
                            -> ty::AutoDerefRef
    {
        match *adjustment {
            probe::AutoDeref(num) => {
                ty::AutoDerefRef {
                    autoderefs: num,
                    autoref: None
                }
            }
            probe::AutoRef(mutability, ref sub_adjustment) => {
                let deref = self.create_ty_adjustment(&**sub_adjustment);
                let region = self.infcx().next_region_var(infer::Autoref(self.span));
                wrap_autoref(deref, |base| ty::AutoPtr(region, mutability, base))
            }
            probe::AutoUnsizeLength(n, ref sub_adjustment) => {
                let deref = self.create_ty_adjustment(&**sub_adjustment);
                wrap_autoref(deref, |base| ty::AutoUnsize(ty::UnsizeLength(n)))
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    //

    fn fresh_receiver_substs(&mut self,
                             self_ty: ty::t,
                             pick: &probe::Pick)
                             -> (subst::Substs, MethodOrigin)
    {
        /*!
         * Returns a set of substitutions for the method *receiver*
         * where all type and region parameters are instantiated with
         * fresh variables. This substitution does not include any
         * parameters declared on the method itself.
         */

        match pick.kind {
            probe::InherentImplPick(impl_def_id) => {
                assert!(ty::impl_trait_ref(self.tcx(), impl_def_id).is_none(),
                        "impl {} is not an inherent impl", impl_def_id);
                let impl_polytype = check::impl_self_ty(self.fcx, self.span, impl_def_id);

                (impl_polytype.substs, MethodStatic(pick.method_ty.def_id))
            }

            probe::ObjectPick(trait_def_id, method_num, real_index) => {
                match ty::get(self_ty).sty {
                    ty::ty_trait(ref data) => {
                        let original_trait_ref = Rc::new(ty::TraitRef::new(data.def_id,
                                                                           data.substs.clone()));
                        let upcast_trait_ref = self.upcast(original_trait_ref, trait_def_id);
                        let substs = upcast_trait_ref.substs.clone();
                        let origin = MethodTraitObject(MethodObject {
                            trait_ref: upcast_trait_ref,
                            object_trait_id: trait_def_id,
                            method_num: method_num,
                            real_index: real_index,
                        });
                        (substs, origin)
                    }
                    _ => {
                        self.tcx().sess.span_bug(
                            self.span,
                            format!("ObjectPick applied to non-object type: {}",
                                    self_ty.repr(self.tcx()))[]);
                    }
                }
            }

            probe::ExtensionImplPick(impl_def_id, method_num) => {
                // The method being invoked is the method as defined on the trait,
                // so return the substitutions from the trait. Consider:
                //
                //     impl<A,B,C> Trait<A,B> for Foo<C> { ... }
                //
                // If we instantiate A, B, and C with $A, $B, and $C
                // respectively, then we want to return the type
                // parameters from the trait ([$A,$B]), not those from
                // the impl ([$A,$B,$C]) not the receiver type ([$C]).
                let impl_polytype = check::impl_self_ty(self.fcx, self.span, impl_def_id);
                let impl_trait_ref = ty::impl_trait_ref(self.tcx(), impl_def_id)
                                     .unwrap()
                                     .subst(self.tcx(), &impl_polytype.substs);
                let origin = MethodTypeParam(MethodParam { trait_ref: impl_trait_ref.clone(),
                                                           method_num: method_num });
                (impl_trait_ref.substs.clone(), origin)
            }

            probe::WhereClausePick(ref trait_ref, method_num) => {
                let origin = MethodTypeParam(MethodParam { trait_ref: (*trait_ref).clone(),
                                                           method_num: method_num });
                (trait_ref.substs.clone(), origin)
            }
        }
    }

    fn instantiate_method_substs(&mut self,
                                 pick: &probe::Pick,
                                 supplied_method_types: Vec<ty::t>)
                                 -> (Vec<ty::t>, Vec<ty::Region>)
    {
        // Determine the values for the generic parameters of the method.
        // If they were not explicitly supplied, just construct fresh
        // variables.
        let num_supplied_types = supplied_method_types.len();
        let num_method_types = pick.method_ty.generics.types.len(subst::FnSpace);
        let method_types = {
            if num_supplied_types == 0u {
                self.fcx.infcx().next_ty_vars(num_method_types)
            } else if num_method_types == 0u {
                span_err!(self.tcx().sess, self.span, E0035,
                    "does not take type parameters");
                self.fcx.infcx().next_ty_vars(num_method_types)
            } else if num_supplied_types != num_method_types {
                span_err!(self.tcx().sess, self.span, E0036,
                    "incorrect number of type parameters given for this method");
                Vec::from_elem(num_method_types, ty::mk_err())
            } else {
                supplied_method_types
            }
        };

        // Create subst for early-bound lifetime parameters, combining
        // parameters from the type and those from the method.
        //
        // FIXME -- permit users to manually specify lifetimes
        let method_regions =
            self.fcx.infcx().region_vars_for_defs(
                self.span,
                pick.method_ty.generics.regions.get_slice(subst::FnSpace));

        (method_types, method_regions)
    }

    fn unify_receivers(&mut self,
                       self_ty: ty::t,
                       method_self_ty: ty::t)
    {
        match self.fcx.mk_subty(false, infer::Misc(self.span), self_ty, method_self_ty) {
            Ok(_) => {}
            Err(_) => {
                self.tcx().sess.span_bug(
                    self.span,
                    format!(
                        "{} was a subtype of {} but now is not?",
                        self_ty.repr(self.tcx()),
                        method_self_ty.repr(self.tcx()))[]);
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    //

    fn instantiate_method_sig(&mut self,
                              pick: &probe::Pick,
                              all_substs: &subst::Substs)
                              -> ty::FnSig
    {
        let ref bare_fn_ty = pick.method_ty.fty;
        let fn_sig = bare_fn_ty.sig.subst(self.tcx(), all_substs);
        self.infcx().replace_late_bound_regions_with_fresh_var(fn_sig.binder_id,
                                                               self.span,
                                                               &fn_sig)
    }

    fn add_obligations(&mut self,
                       pick: &probe::Pick,
                       all_substs: &subst::Substs) {
        // FIXME(DST). Super hack. For a method on a trait object
        // `Trait`, the generic signature requires that
        // `Self:Trait`. Since, for an object, we bind `Self` to the
        // type `Trait`, this leads to an obligation
        // `Trait:Trait`. Until such time we DST is fully implemented,
        // that obligation is not necessarily satisfied. (In the
        // future, it would be.)
        //
        // To sidestep this, we overwrite the binding for `Self` with
        // `err` (just for trait objects) when we generate the
        // obligations.  This causes us to generate the obligation
        // `err:Trait`, and the error type is considered to implement
        // all traits, so we're all good. Hack hack hack.
        match pick.kind {
            probe::ObjectPick(..) => {
                let mut temp_substs = all_substs.clone();
                temp_substs.types.get_mut_slice(subst::SelfSpace)[0] = ty::mk_err();
                self.fcx.add_obligations_for_parameters(
                    traits::ObligationCause::misc(self.span),
                    &temp_substs,
                    &pick.method_ty.generics);
            }
            _ => {
                self.fcx.add_obligations_for_parameters(
                    traits::ObligationCause::misc(self.span),
                    all_substs,
                    &pick.method_ty.generics);
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // MISCELLANY

    fn tcx(&self) -> &'a ty::ctxt<'tcx> {
        self.fcx.tcx()
    }

    fn infcx(&self) -> &'a InferCtxt<'a, 'tcx> {
        self.fcx.infcx()
    }

    fn enforce_drop_trait_limitations(&self, pick: &probe::Pick) {
        // Disallow calls to the method `drop` defined in the `Drop` trait.
        match pick.method_ty.container {
            ty::TraitContainer(trait_def_id) => {
                if Some(trait_def_id) == self.tcx().lang_items.drop_trait() {
                    span_err!(self.tcx().sess, self.span, E0040,
                              "explicit call to destructor");
                }
            }
            ty::ImplContainer(..) => {
                // Since `drop` is a trait method, we expect that any
                // potential calls to it will wind up in the other
                // arm. But just to be sure, check that the method id
                // does not appear in the list of destructors.
                assert!(!self.tcx().destructors.borrow().contains(&pick.method_ty.def_id));
            }
        }
    }

    fn upcast(&mut self,
              source_trait_ref: Rc<ty::TraitRef>,
              target_trait_def_id: ast::DefId)
              -> Rc<ty::TraitRef>
    {
        for super_trait_ref in traits::supertraits(self.tcx(), source_trait_ref.clone()) {
            if super_trait_ref.def_id == target_trait_def_id {
                return super_trait_ref;
            }
        }

        self.tcx().sess.span_bug(
            self.span,
            format!("cannot upcast `{}` to `{}`",
                    source_trait_ref.repr(self.tcx()),
                    target_trait_def_id.repr(self.tcx()))[]);
    }
}

fn wrap_autoref(mut deref: ty::AutoDerefRef,
                base_fn: |Option<Box<ty::AutoRef>>| -> ty::AutoRef)
                -> ty::AutoDerefRef {
    let autoref = mem::replace(&mut deref.autoref, None);
    let autoref = autoref.map(|r| box r);
    deref.autoref = Some(base_fn(autoref));
    deref
}
