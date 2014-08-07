// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Inherent method search: See doc.rs for documentation */

use middle::subst::ParamSpace;
use middle::traits;
use middle::traits::{EvaluationResult, EvaluatedToMatch, EvaluatedToUnmatch,
                     EvaluatedToAmbiguity};
use middle::traits::{Obligation, Selection, VtableImpl, VtableParam};
use middle::ty;
use middle::typeck::check::{deref, FnCtxt};
use std::rc::Rc;
use syntax::ast;
use util::common::ErrorReported;
use util::ppaux::{Repr, UserString};

use super::MethodInfo;

pub fn search_inherent_methods(fcx: &FnCtxt,
                               call_expr: &ast::Expr,
                               _self_expr: &ast::Expr,
                               self_ty: ty::t,
                               method_name: ast::Name)
                               -> Result<Option<MethodInfo>, ErrorReported>
{
    let mut inherent_test = InherentTest { fcx: fcx,
                                           call_expr: call_expr,
                                           method_name: method_name };

    match deref::method_autoderef_loop(fcx, call_expr.span, self_ty,
                                       &mut inherent_test) {
        deref::FoundMatch(xform_ty, selection) => {
            Ok(Some(MethodInfo { xform_ty: xform_ty,
                                 selection: selection }))
        }
        deref::FoundReportedError => {
            Err(ErrorReported)
        }
        deref::FoundNoMatch(_xform_ty) => {
            // possible optimization: pass _xform_ty through to
            // search_trait_methods to avoid repeating autoderef loop.
            Ok(None)
        }
    }
}

struct InherentTest<'a> {
    fcx: &'a FnCtxt<'a>,
    call_expr: &'a ast::Expr,
    method_name: ast::Name,
}

impl<'a> InherentTest<'a> {
    fn tcx(&self) -> &'a ty::ctxt {
        self.fcx.tcx()
    }
}

impl<'a> deref::Test<Selection> for InherentTest<'a> {
    fn test(&mut self,
            self_ty: ty::t)
            -> Result<Option<Selection>, ErrorReported>
    {
        debug!("test for inherent method `{}` defined on type `{}`",
               self.method_name,
               self_ty.repr(self.tcx()));

        match ty::get(self_ty).sty {
            ty::ty_enum(def_id, _) | ty::ty_struct(def_id, _) => {
                self.test_nominal_type(self_ty, def_id)
            }

            ty::ty_param(ref p) => {
                self.test_param_type(self_ty, p)
            }

            ty::ty_trait(ref _ty_trait) => {
                fail!("NYI") // NDM
            }

            _ => {
                Ok(None)
            }
        }
    }
}

impl<'a> InherentTest<'a> {
    fn test_nominal_type(&mut self,
                         self_ty: ty::t,
                         def_id: ast::DefId)
                         -> Result<Option<Selection>, ErrorReported>
    {
        /*!
         * Check for inherent methods defined on the enum/struct
         * with def-id `def_id`
         */

        debug!("nominal type identified: `{}`", def_id.repr(self.tcx()));

        let inherent_impls = self.tcx().inherent_impls.borrow();

        let mut applicable_impl_dids = Vec::new();
        let mut all_definite = true;
        for &did in inherent_impls.find(&def_id)
            .move_iter()
            .flat_map(|dids| dids.iter())
        {
            match self.evaluate_inherent_impl(did, self_ty) {
                EvaluatedToMatch => {
                    debug!("did={} definitely applicable", did);
                    applicable_impl_dids.push(did);
                }
                EvaluatedToAmbiguity => {
                    debug!("did={} not applicable", did);
                    applicable_impl_dids.push(did);
                    all_definite = false;
                }
                EvaluatedToUnmatch => {
                    debug!("did={} maybe applicable", did);
                }
            }
        }

        if applicable_impl_dids.len() == 0 {
            return Ok(None);
        }

        if applicable_impl_dids.len() > 1 {
            return Err(self.report_ambiguity(self_ty,
                                             &applicable_impl_dids));
        }

        if !all_definite {
            return Err(self.report_ambiguity(self_ty,
                                             &applicable_impl_dids));
        }

        // Method is defined in exactly one applicable impl. Yay!
        assert_eq!(applicable_impl_dids.len(), 1);

        let impl_def_id = *applicable_impl_dids.get(0);
        let impl_vtable = self.confirm_impl(impl_def_id, self_ty);
        Ok(Some(VtableImpl(impl_vtable)))
    }

    fn test_param_type(&self,
                       self_ty: ty::t,
                       param_ty: &ty::ParamTy)
                       -> Result<Option<Selection>, ErrorReported>
    {
        /*!
         * We consider methods associated with trait bounds to be
         * inherent methods of the parameter type. For example,
         * in this code...
         *
         *     use m;
         *
         *     fn foo<T: m::Bar>(...) { ... }
         *
         * ...the methods defined on `m::Bar` are inherent to `T`,
         * even though they are defined on a trait. Otherwise,
         * they could not be called, because `m::Bar` is not in scope.
         *
         * This also helps make the autoderef rules work out better
         * for traits where the trait is implemented for every
         * possible type:
         *
         *     fn foo<T: Ord>(x: &T, y: &T) {
         *         x.cmp(y) // without this rule, would fail to typechk
         *     }
         *
         * The above example fails to type check without this
         * inherent methods condition because the `cmp` method
         * matches with `Self=&T`, and hence it expects an
         * argument of type `&&y`.  This is surprising and
         * basically never what you wanted.
         *
         * CONSIDER -- This is a bit odd when you consider a
         * where-clause based model, because a where clause like `T :
         * Trait` defines an inherent method, but a where clause like
         * `(T, int) : Trait` does not.
         */

        debug!("test_param_type(self_ty={})",
               self_ty.repr(self.tcx()));

        for &space in ParamSpace::all().iter() {
            for (i, caller_obligation) in
                self.fcx.inh.param_env.caller_obligations
                                      .get_slice(space)
                                      .iter()
                                      .enumerate()
            {
                // Test for an obligation like T : Bar
                let caller_bound = &caller_obligation.trait_ref;
                let caller_self_ty = caller_bound.substs.self_ty().unwrap();
                debug!("caller_obligation={}",
                       caller_obligation.repr(self.tcx()));

                match ty::get(caller_self_ty).sty {
                    ty::ty_param(ref caller_param_ty) => {
                        if param_ty != caller_param_ty {
                            continue;
                        }
                    }
                    _ => { continue; }
                }

                // Check whether the method is defined in the
                // bound trait (or a supertrait)
                let caller_bound = (*caller_bound).clone();
                match traits::search_trait_and_supertraits_from_bound(
                    self.fcx.tcx(), space, i, caller_bound,
                    |d| self.trait_defines_method_directly(d))
                {
                    Some(param) => {
                        debug!("found match param={}", param.repr(self.tcx()));
                        return Ok(Some(VtableParam(param)));
                    }

                    None => {
                        return Ok(None);
                    }
                }
            }
        }

        return Ok(None);
    }

    fn evaluate_inherent_impl(&self,
                              impl_def_id: ast::DefId,
                              self_ty: ty::t)
                              -> EvaluationResult
    {
        /*!
         * True if an inherent impl may apply to this call.
         */

        // Does the impl define the method we are looking for?
        if self.method_from_impl(impl_def_id).is_none() {
            return traits::EvaluatedToUnmatch;
        }

        // Are the conditions on the impl (maybe) met?
        traits::evaluate_impl(self.fcx.infcx(),
                              &self.fcx.inh.param_env,
                              self.call_expr.span,
                              impl_def_id,
                              self_ty)
    }

    fn method_from_impl(&self, def_id: ast::DefId) -> Option<Rc<ty::Method>> {
        let impl_methods = self.tcx().impl_methods.borrow();
        let methods = impl_methods.get(&def_id);
        methods.iter().map(|&def_id| ty::method(self.tcx(), def_id))
                      .find(|m| m.ident.name == self.method_name)
    }

    fn trait_defines_method_directly(&self, trait_def_id: ast::DefId) -> bool {
        ty::trait_methods(self.fcx.tcx(), trait_def_id)
            .iter()
            .any(|m| m.ident.name == self.method_name)
    }

    fn report_ambiguity(&mut self,
                        self_ty: ty::t,
                        applicable_impl_dids: &Vec<ast::DefId>)
                        -> ErrorReported
    {
        /*!
         * Coherence *should* ensure that the set of inherent impls
         * cannot be ambiguous, so this almost certainly means that more
         * type information is required.
         */

        assert!(applicable_impl_dids.len() >= 1);

        if !ty::type_needs_infer(self_ty) && self.tcx().sess.err_count() == 0 {
            // Ambiguity. Coherence should have reported an error.
            self.tcx().sess.span_bug(
                self.call_expr.span,
                format!("ambiguity for inherent impl for `{}` of {}",
                        self.method_name.user_string(self.tcx()),
                        self_ty.user_string(self.tcx())).as_slice());
        }

        self.tcx().sess.span_err(
            self.call_expr.span,
            format!("insufficient type information to select \
                     the correct impl for the method `{}` \
                     invoked on the type `{}`; type annotations \
                     required",
                    self.method_name.user_string(self.tcx()),
                    self_ty.user_string(self.tcx())).as_slice());

        // If the inherent impls are local to this crate, give spans.
        // Otherwise, not much we can do.
        let mut local_impl_dids =
            applicable_impl_dids
            .iter()
            .filter(|did| did.krate == ast::LOCAL_CRATE)
            .enumerate();
        for (i, &def_id) in local_impl_dids {
            let span = self.tcx().map.span(def_id.node);
            self.tcx().sess.span_note(span,
                                      format!("candidate {} located here",
                                              i).as_slice());
        }

        ErrorReported
    }

    fn confirm_impl(&mut self,
                    impl_def_id: ast::DefId,
                    self_ty: ty::t)
                    -> VtableImpl<Obligation>
    {
        match traits::select_inherent_impl(self.fcx.infcx(),
                                           &self.fcx.inh.param_env,
                                           self.call_expr.span,
                                           impl_def_id,
                                           self_ty) {
            Ok(Some(vtable)) => vtable,
            ref r => {
                self.tcx().sess.span_bug(
                    self.call_expr.span,
                    format!("impl `{}` evaluated to a match with `{}` \
                             but could not be confirmed: {}",
                            impl_def_id,
                            self_ty.repr(self.fcx.tcx()),
                            r).as_slice());
            }
        }
    }
}
