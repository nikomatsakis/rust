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

use middle::traits;
use middle::traits::{Vtable, DefinitelyApplicable, MaybeApplicable,
                     NotApplicable, Overflow, ResolvedTo};
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

    match deref::autoderef_loop(fcx, call_expr.span, self_ty,
                                &mut inherent_test) {
        deref::FoundMatch(xform_ty, FromImpl(impl_vtable, _method)) => {
            let impl_origin = Vtable(impl_vtable, None);
            //                                    ^~~~
            //
            // None is a suitable value here: this field is
            // supposed to record deferred errors that
            // occurred matching the output type parameters of
            // the trait. In the case of an inherent method,
            // there are no output parameters to match.

            Ok(Some(MethodInfo { xform_ty: xform_ty,
                                 origin: impl_origin }))
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

enum InherentResult {
    FromImpl(Vtable, Rc<ty::Method>),
}

impl<'a> InherentTest<'a> {
    fn tcx(&self) -> &'a ty::ctxt {
        self.fcx.tcx()
    }
}

impl<'a> deref::Test<InherentResult> for InherentTest<'a> {
    fn test(&mut self,
            self_ty: ty::t)
            -> Result<Option<InherentResult>, ErrorReported>
    {
        match ty::get(self_ty).sty {
            ty::ty_enum(def_id, _) | ty::ty_struct(def_id, _) => {
                let inherent_impls = self.tcx().inherent_impls.borrow();

                let mut applicable_impl_dids = Vec::new();
                for &did in inherent_impls.find(&def_id)
                                          .move_iter()
                                          .flat_map(|dids| dids.iter())
                {
                    if try!(self.evaluate_impl(did, self_ty)) {
                        applicable_impl_dids.push(did);
                    }
                }

                if applicable_impl_dids.len() == 0 {
                    return Ok(None);
                }

                if applicable_impl_dids.len() > 1 {
                    return Err(self.report_ambiguity(self_ty,
                                                     &applicable_impl_dids));
                }

                // Method is defined in exactly one applicable impl. Yay!
                assert_eq!(applicable_impl_dids.len(), 1);

                let impl_def_id = *applicable_impl_dids.get(0);
                let impl_vtable = self.confirm_impl(impl_def_id, self_ty);
                let method = self.method_from_impl(impl_def_id).unwrap();
                Ok(Some(FromImpl(impl_vtable, method)))
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
    fn evaluate_impl(&self,
                     impl_def_id: ast::DefId,
                     self_ty: ty::t)
                     -> Result<bool, ErrorReported> {
        /*!
         * True if an inherent impl may apply to this call.
         */

        // Does the impl define the method we are looking for?
        if self.method_from_impl(impl_def_id).is_none() {
            return Ok(false);
        }

        // Are the conditions on the impl (maybe) met?
        match traits::evaluate_impl(self.fcx.infcx(),
                                    &self.fcx.inh.param_env,
                                    self.call_expr.span,
                                    impl_def_id,
                                    self_ty) {
            DefinitelyApplicable | MaybeApplicable => Ok(true),
            NotApplicable => Ok(false),
            Overflow => Err(self.report_overflow(self_ty)),
        }
    }

    fn method_from_impl(&self, def_id: ast::DefId) -> Option<Rc<ty::Method>> {
        let impl_methods = self.tcx().impl_methods.borrow();
        let methods = impl_methods.get(&def_id);
        methods.iter().map(|&def_id| ty::method(self.tcx(), def_id))
                      .find(|m| m.ident.name == self.method_name)
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

        assert!(applicable_impl_dids.len() > 1);

        if !ty::type_needs_infer(self_ty) {
            // Ambiguity. Coherence should have reported an error.
            assert!(self.tcx().sess.err_count() > 0);
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

    fn report_overflow(&self, self_ty: ty::t) -> ErrorReported {
        self.tcx().sess.span_err(
            self.call_expr.span,
            format!(
                "overflow encountered evaluating applicability of \
                 inherent impls for type `{}`",
                self_ty.user_string(self.tcx())).as_slice());
        ErrorReported
    }

    fn confirm_impl(&mut self,
                    impl_def_id: ast::DefId,
                    self_ty: ty::t)
                    -> Vtable
    {
        match traits::match_inherent_impl(self.fcx.infcx(),
                                          &self.fcx.inh.param_env,
                                          self.call_expr.span,
                                          impl_def_id,
                                          self_ty) {
            Some(ResolvedTo(vtable)) => vtable,
            _ => {
                self.tcx().sess.span_bug(
                    self.call_expr.span,
                    format!("impl `{}` evaluated to a match with `{}` \
                             but could not be confirmed",
                            impl_def_id,
                            self_ty.repr(self.fcx.tcx())).as_slice());
            }
        }
    }
}
