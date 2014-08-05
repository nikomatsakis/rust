// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*! Trait method search: See doc.rs for documentation */

use middle::subst::Subst;
use middle::traits;
use middle::traits::{Vtable, Obligation, Selection, SelectionResult};
use middle::traits::{EvaluationResult, EvaluatedToMatch, EvaluatedToAmbiguity};
use middle::ty;
use middle::typeck::check::deref;
use middle::typeck::check::deref::Test;
use middle::typeck::check::FnCtxt;
use middle::typeck::check::vtable;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use util::common::ErrorReported;
use util::ppaux::{Repr, UserString};

use super::MethodInfo;

pub fn search_trait_methods(fcx: &FnCtxt,
                            call_expr: &ast::Expr,
                            self_expr: &ast::Expr,
                            self_ty: ty::t,
                            method_name: ast::Name)
                            -> Result<Option<MethodInfo>, ErrorReported>
{
    /*!
     * Searches to find some type T, derived by autoderefencing `self_ty`,
     * that implements some trait TR in scope, where TR defines a method
     * named `method_name`.
     */

    // Determine traits that are in scope and which define `method_name`
    let mut applicable_traits: Vec<ast::DefId> =
        fcx.ccx.trait_map.find(&call_expr.id)
        .move_iter()
        .flat_map(|trait_def_ids| trait_def_ids.iter())
        .filter(|&&trait_def_id| trait_defines_method(fcx,
                                                      trait_def_id,
                                                      method_name))
        .map(|&trait_def_id| trait_def_id)
        .collect();

    // Remove duplicates.
    applicable_traits.sort();
    applicable_traits.dedup();

    search_methods_from_traits(fcx, call_expr.span, self_expr, self_ty,
                               method_name, applicable_traits.as_slice())
}

pub fn search_methods_from_traits(fcx: &FnCtxt,
                                  call_span: Span,
                                  _self_expr: &ast::Expr,
                                  self_ty: ty::t,
                                  method_name: ast::Name,
                                  applicable_traits: &[ast::DefId])
                                  -> Result<Option<MethodInfo>, ErrorReported>
{
    /*!
     * Searches to find some type T, derived by autoderefencing `self_ty`,
     * that implements any trait in `applicable_traits` (each of which
     * should define a method named `method_name`.).
     */

    let mut trait_test = TraitTest { fcx: fcx,
                                     call_span: call_span,
                                     method_name: method_name,
                                     applicable_traits: applicable_traits };

    // If there are no traits in scope that even define a method with
    // the given name, report a more specific error with (hopefully)
    // helpful suggestion!
    if applicable_traits.len() == 0 {
        trait_test.report_no_applicable_traits(self_ty);
        Err(ErrorReported)
    } else {
        match deref::method_autoderef_loop(fcx, call_span, self_ty, &mut trait_test) {
            deref::FoundMatch(xform_ty, TraitResult { selection, .. }) => {
                Ok(Some(MethodInfo { xform_ty: xform_ty,
                                     selection: selection }))
            }
            deref::FoundReportedError => {
                Err(ErrorReported)
            }
            deref::FoundNoMatch(_) => {
                Ok(None)
            }
        }
    }
}

pub fn test_methods_from_traits(fcx: &FnCtxt,
                                call_span: Span,
                                _self_expr: &ast::Expr,
                                self_ty: ty::t,
                                method_name: ast::Name,
                                applicable_traits: &[ast::DefId])
                                -> Result<Option<MethodInfo>, ErrorReported>
{
    /*!
     * Tests where `self_ty` implements any trait in `applicable_traits`
     * that defines a method named `method_name`. No autoderefencing.
     */

    assert!(applicable_traits.len() > 0);

    let mut trait_test = TraitTest { fcx: fcx,
                                     call_span: call_span,
                                     method_name: method_name,
                                     applicable_traits: applicable_traits };

    match try!(trait_test.test(self_ty)) {
        None => Ok(None),
        Some(TraitResult { selection, .. }) => {
            let xform_ty = deref::root_type(self_ty);
            Ok(Some(MethodInfo { xform_ty: xform_ty,
                                 selection: selection }))
        }
    }
}

fn trait_defines_method(fcx: &FnCtxt,
                        trait_def_id: ast::DefId,
                        method_name: ast::Name)
                        -> bool
{
    if ty::trait_methods(fcx.tcx(), trait_def_id)
        .iter()
        .any(|m| m.ident.name == method_name)
    {
        return true;
    }

    ty::trait_supertraits(fcx.tcx(), trait_def_id)
        .iter()
        .any(|r| trait_defines_method(fcx, r.def_id, method_name))
}

struct TraitTest<'a> {
    fcx: &'a FnCtxt<'a>,
    call_span: Span,
    method_name: ast::Name,
    applicable_traits: &'a [ast::DefId],
}

struct TraitResult {
    selection: Selection,
}

impl<'a> Test<TraitResult> for TraitTest<'a> {
    fn test(&mut self, self_ty: ty::t) -> Result<Option<TraitResult>,
                                                 ErrorReported>
    {
        // Identify those in-scope traits that might match against `self_ty`
        let mut traits: Vec<(Obligation, EvaluationResult)> =
            self.applicable_traits
            .iter()
            .map(|&def_id| self.obligation_for_trait(def_id, self_ty))
            .map(|oblig| self.evaluate_obligation(oblig))
            .filter(|&(_, eval)| eval.potentially_applicable())
            .collect();

        // No match!
        if traits.len() == 0 {
            return Ok(None);
        }

        // If anything is maybe applicable, that's ambiguity.
        match traits.iter().find(|&&(_, eval)| eval == EvaluatedToAmbiguity) {
            None => { }
            Some(&(ref oblig, _)) => {
                return Err(self.report_ambiguity(oblig));
            }
        }

        // If multiple things are definitely applicable, that's ambiguity too.
        if traits.len() > 1 {
            return Err(self.report_multiple(self_ty,
                                            traits.iter().map(|&(ref a, _)| a)));
        }

        // Exactly one definite match.
        assert_eq!(traits.len(), 1);
        let (obligation, eval) = traits.pop().unwrap();
        assert_eq!(eval, EvaluatedToMatch);
        match self.try_select_obligation(&obligation) {
            Ok(Some(selection)) => {
                Ok(Some(TraitResult { selection: selection }))
            }
            Err(ref e) => {
                vtable::report_selection_error(self.fcx, &obligation, e);
                Err(ErrorReported)
            }
            Ok(None) => {
                self.tcx().sess.span_bug(
                    self.call_span,
                    format!("obligation `{}` was resolvable but is now ambiguous",
                            obligation.repr(self.tcx())).as_slice());
            }
        }
    }
}

impl<'a> TraitTest<'a> {
    fn tcx(&self) -> &'a ty::ctxt {
        self.fcx.tcx()
    }

    fn obligation_for_trait(&self,
                            trait_def_id: ast::DefId,
                            self_ty: ty::t)
                            -> Obligation
    {
        let trait_def = ty::lookup_trait_def(self.tcx(), trait_def_id);
        let substs =
            self.fcx.infcx().fresh_substs_for_trait(self.call_span,
                                                    &trait_def.generics,
                                                    self_ty);
        let trait_ref = trait_def.trait_ref.subst(self.tcx(), &substs);
        Obligation::new(self.call_span, trait_ref)
    }

    fn evaluate_obligation(&self,
                           obligation: Obligation)
                           -> (Obligation, EvaluationResult)
    {
        let eval = traits::evaluate_obligation(self.fcx.infcx(),
                                               &self.fcx.inh.param_env,
                                               &obligation);
        debug!("evaluate_obligation: {} -> {}",
               obligation.repr(self.tcx()),
               eval);
        (obligation, eval)
    }

    fn try_select_obligation(&self,
                             obligation: &Obligation)
                             -> SelectionResult<Vtable<Obligation>>
    {
        traits::try_select_obligation(self.fcx.infcx(),
                                      &self.fcx.inh.param_env,
                                      obligation)
    }

    fn report_no_applicable_traits(&self, self_ty: ty::t) -> ErrorReported {
        self.tcx().sess.span_err(
            self.call_span,
            format!(
                "the method `{}` is not defined on the type `{}` \
                nor any of the traits in scope; \
                you may need to import the trait where the method is defined",
                self.method_name.user_string(self.tcx()),
                self_ty.user_string(self.tcx())).as_slice());
        ErrorReported
    }

    fn report_ambiguity(&self, obligation: &Obligation) -> ErrorReported {
        vtable::maybe_report_ambiguity(self.fcx, obligation);
        ErrorReported
    }

    fn report_multiple<'a,I:Iterator<&'a Obligation>>(&self,
                                                      self_ty: ty::t,
                                                      obligations: I)
                                                      -> ErrorReported
    {
        self.tcx().sess.span_err(
            self.call_span,
            format!("multiple traits supply the method `{}` and are \
                     potentially applicable to type `{}`",
                    self.method_name.user_string(self.tcx()),
                    self_ty.user_string(self.tcx())).as_slice());

        if ty::type_needs_infer(self_ty) {
            self.tcx().sess.span_note(
                self.call_span,
                "more type annotations may be required");
        }

        for (i, obligation) in obligations.enumerate() {
            self.tcx().sess.span_note(
                self.call_span,
                format!(
                    "candidate {} is the trait `{}`",
                    i,
                    obligation.trait_ref.user_string(self.tcx())).as_slice());
        }

        ErrorReported
   }
}
