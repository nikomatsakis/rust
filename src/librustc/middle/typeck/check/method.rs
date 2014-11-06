// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!

# Method lookup

Method lookup can be rather complex due to the interaction of a number
of factors, such as self types, autoderef, trait lookup, etc.  The
algorithm is divided into two parts: candidate collection and
candidate selection.

## Candidate collection

A `Candidate` is a method item that might plausibly be the method
being invoked.  Candidates are grouped into two kinds, inherent and
extension.  Inherent candidates are those that are derived from the
type of the receiver itself.  So, if you have a receiver of some
nominal type `Foo` (e.g., a struct), any methods defined within an
impl like `impl Foo` are inherent methods.  Nothing needs to be
imported to use an inherent method, they are associated with the type
itself (note that inherent impls can only be defined in the same
module as the type itself).

Inherent candidates are not always derived from impls.  If you have a
trait instance, such as a value of type `Box<ToString>`, then the trait
methods (`to_string()`, in this case) are inherently associated with it.
Another case is type parameters, in which case the methods of their
bounds are inherent.

Extension candidates are derived from imported traits.  If I have the
trait `ToString` imported, and I call `to_string()` on a value of type `T`,
then we will go off to find out whether there is an impl of `ToString`
for `T`.  These kinds of method calls are called "extension methods".
They can be defined in any module, not only the one that defined `T`.
Furthermore, you must import the trait to call such a method.

For better or worse, we currently give weight to inherent methods over
extension methods during candidate selection (below).

## Candidate selection

Once we know the set of candidates, we can go off and try to select
which one is actually being called.  We do this by taking the type of
the receiver, let's call it R, and checking whether it matches against
the expected receiver type for each of the collected candidates.  We
first check for inherent candidates and see whether we get exactly one
match (zero means keep searching, more than one is an error).  If so,
we return that as the candidate.  Otherwise we search the extension
candidates in the same way.

If find no matching candidate at all, we proceed to auto-deref the
receiver type and search again.  We keep doing that until we cannot
auto-deref any longer.  At each step, we also check for candidates
based on "autoptr", which if the current type is `T`, checks for `&mut
T`, `&const T`, and `&T` receivers.  Finally, at the very end, we will
also try autoslice, which converts `~[]` to `&[]` (there is no point
at trying autoslice earlier, because no autoderefable type is also
sliceable).

## Why two phases?

You might wonder why we first collect the candidates and then select.
Both the inherent candidate collection and the candidate selection
proceed by progressively deref'ing the receiver type, after all.  The
answer is that two phases are needed to elegantly deal with explicit
self.  After all, if there is an impl for the type `Foo`, it can
define a method with the type `Box<self>`, which means that it expects a
receiver of type `Box<Foo>`.  If we have a receiver of type `Box<Foo>`, but we
waited to search for that impl until we have deref'd the `Box` away and
obtained the type `Foo`, we would never match this method.

*/

use super::method2;
pub use super::method2::MethodError;
pub use super::method2::CandidateSource;
pub use super::method2::NoMatch;
pub use super::method2::Ambiguity;
pub use super::method2::ImplSource;
pub use super::method2::TraitSource;

use middle::subst;
use middle::subst::{Subst};
use middle::traits;
use middle::ty::*;
use middle::ty;
use middle::typeck::astconv::AstConv;
use middle::typeck::check::{FnCtxt};
use middle::typeck::check::{impl_self_ty};
use middle::typeck::check::vtable::select_new_fcx_obligations;
use middle::typeck::{MethodCallee};
use middle::typeck::{MethodParam, MethodTypeParam};
use middle::typeck::check::vtable;
use util::ppaux::{Repr, UserString};

use std::rc::Rc;
use syntax::ast::{DefId};
use syntax::ast;
use syntax::codemap::Span;

pub fn lookup<'a, 'tcx>(
    fcx: &'a FnCtxt<'a, 'tcx>,

    // In a call `a.b::<X, Y, ...>(...)`:
    expr: &ast::Expr,                   // The expression `a.b(...)`.
    self_expr: &'a ast::Expr,           // The expression `a`.
    m_name: ast::Name,                  // The name `b`.
    self_ty: ty::t,                     // The type of `a`.
    supplied_tps: &'a [ty::t])          // The list of types X, Y, ... .
    -> Result<MethodCallee, MethodError>
{
    method2::lookup(fcx,
                    expr.span,
                    m_name,
                    self_ty,
                    supplied_tps.to_vec(),
                    expr.id,
                    self_expr)
}

pub fn lookup_in_trait<'a, 'tcx>(
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    self_expr: Option<&'a ast::Expr>,
    m_name: ast::Name,
    trait_def_id: DefId,
    self_ty: ty::t,
    opt_input_types: Option<Vec<ty::t>>)
    -> Option<MethodCallee>
{
    lookup_in_trait_adjusted(fcx, span, self_expr, m_name, trait_def_id,
                             ty::AutoDerefRef { autoderefs: 0, autoref: None },
                             self_ty, opt_input_types)
}

pub fn lookup_in_trait_adjusted<'a, 'tcx>(
    fcx: &'a FnCtxt<'a, 'tcx>,
    span: Span,
    self_expr: Option<&'a ast::Expr>,
    m_name: ast::Name,
    trait_def_id: DefId,
    autoderefref: ty::AutoDerefRef,
    self_ty: ty::t,
    opt_input_types: Option<Vec<ty::t>>)
    -> Option<MethodCallee>
{
    debug!("method lookup_in_trait(self_ty={}, self_expr={}, m_name={}, trait_def_id={})",
           self_ty.repr(fcx.tcx()),
           self_expr.repr(fcx.tcx()),
           m_name.repr(fcx.tcx()),
           trait_def_id.repr(fcx.tcx()));

    let trait_def = ty::lookup_trait_def(fcx.tcx(), trait_def_id);

    let expected_number_of_input_types = trait_def.generics.types.len(subst::TypeSpace);
    let input_types = match opt_input_types {
        Some(input_types) => {
            assert_eq!(expected_number_of_input_types, input_types.len());
            input_types
        }

        None => {
            fcx.inh.infcx.next_ty_vars(expected_number_of_input_types)
        }
    };

    let number_assoc_types = trait_def.generics.types.len(subst::AssocSpace);
    let assoc_types = fcx.inh.infcx.next_ty_vars(number_assoc_types);

    assert_eq!(trait_def.generics.types.len(subst::FnSpace), 0);
    assert!(trait_def.generics.regions.is_empty());

    // Construct a trait-reference `self_ty : Trait<input_tys>`
    let substs = subst::Substs::new_trait(input_types, Vec::new(), assoc_types, self_ty);
    let trait_ref = Rc::new(ty::TraitRef::new(trait_def_id, substs));

    // Construct an obligation
    let obligation = traits::Obligation::misc(span, trait_ref.clone());

    // Now we want to know if this can be matched
    let mut selcx = traits::SelectionContext::new(fcx.infcx(),
                                                  &fcx.inh.param_env,
                                                  fcx);
    if !selcx.evaluate_obligation_intracrate(&obligation) {
        debug!("--> Cannot match obligation");
        return None; // Cannot be matched, no such method resolution is possible.
    }

    // Trait must have a method named `m_name` and it should not have
    // type parameters or early-bound regions.
    let tcx = fcx.tcx();
    let (method_num, method_ty) = trait_method(tcx, trait_def_id, m_name).unwrap();
    assert_eq!(method_ty.generics.types.len(subst::FnSpace), 0);
    assert_eq!(method_ty.generics.regions.len(subst::FnSpace), 0);

    // Substitute the trait parameters into the method type and
    // instantiate late-bound regions to get the actual method type.
    let ref bare_fn_ty = method_ty.fty;
    let fn_sig = bare_fn_ty.sig.subst(tcx, &trait_ref.substs);
    let fn_sig = fcx.infcx().replace_late_bound_regions_with_fresh_var(fn_sig.binder_id,
                                                                       span,
                                                                       &fn_sig);
    let transformed_self_ty = fn_sig.inputs[0];
    let fty = ty::mk_bare_fn(tcx, ty::BareFnTy {
        sig: fn_sig,
        fn_style: bare_fn_ty.fn_style,
        abi: bare_fn_ty.abi.clone(),
    });

    debug!("matched method fty={} obligation={}",
           fty.repr(fcx.tcx()),
           obligation.repr(fcx.tcx()));

    // Register obligations for the parameters.  This will include the
    // `Self` parameter, which in turn has a bound of the main trait,
    // so this also effectively registers `obligation` as well.  (We
    // used to register `obligation` explicitly, but that resulted in
    // double error messages being reported.)
    fcx.add_obligations_for_parameters(
        traits::ObligationCause::misc(span),
        &trait_ref.substs,
        &method_ty.generics);

    // FIXME(#18653) -- Try to resolve obligations, giving us more
    // typing information, which can sometimes be needed to avoid
    // pathological region inference failures.
    vtable::select_new_fcx_obligations(fcx);

    // Insert any adjustments needed (always an autoref of some mutability).
    match self_expr {
        None => { }

        Some(self_expr) => {
            debug!("inserting adjustment if needed (self-id = {}, \
                   base adjustment = {}, explicit self = {})",
                   self_expr.id, autoderefref, method_ty.explicit_self);

            match method_ty.explicit_self {
                ty::ByValueExplicitSelfCategory => {
                    // Trait method is fn(self), no transformation needed.
                    if !autoderefref.is_identity() {
                        fcx.write_adjustment(
                            self_expr.id,
                            span,
                            ty::AdjustDerefRef(autoderefref));
                    }
                }

                ty::ByReferenceExplicitSelfCategory(..) => {
                    // Trait method is fn(&self) or fn(&mut self), need an
                    // autoref. Pull the region etc out of the type of first argument.
                    match ty::get(transformed_self_ty).sty {
                        ty::ty_rptr(region, ty::mt { mutbl, ty: _ }) => {
                            let ty::AutoDerefRef { autoderefs, autoref } = autoderefref;
                            let autoref = autoref.map(|r| box r);
                            fcx.write_adjustment(
                                self_expr.id,
                                span,
                                ty::AdjustDerefRef(ty::AutoDerefRef {
                                    autoderefs: autoderefs,
                                    autoref: Some(ty::AutoPtr(region, mutbl, autoref))
                                }));
                        }

                        _ => {
                            fcx.tcx().sess.span_bug(
                                span,
                                format!(
                                    "trait method is &self but first arg is: {}",
                                    transformed_self_ty.repr(fcx.tcx())).as_slice());
                        }
                    }
                }

                _ => {
                    fcx.tcx().sess.span_bug(
                        span,
                        format!(
                            "unexpected explicit self type in operator method: {}",
                            method_ty.explicit_self).as_slice());
                }
            }
        }
    }

    let callee = MethodCallee {
        origin: MethodTypeParam(MethodParam{trait_ref: trait_ref.clone(),
                                            method_num: method_num}),
        ty: fty,
        substs: trait_ref.substs.clone()
    };

    debug!("callee = {}", callee.repr(fcx.tcx()));

    Some(callee)
}

pub fn report_error(fcx: &FnCtxt,
                    span: Span,
                    rcvr_ty: ty::t,
                    method_name: ast::Name,
                    error: MethodError)
{
    match error {
        NoMatch(static_sources) => {
            let cx = fcx.tcx();
            let method_ustring = method_name.user_string(cx);

            // True if the type is a struct and contains a field with
            // the same name as the not-found method
            let is_field = match ty::get(rcvr_ty).sty {
                ty_struct(did, _) =>
                    ty::lookup_struct_fields(cx, did)
                        .iter()
                        .any(|f| f.name.user_string(cx) == method_ustring),
                _ => false
            };

            fcx.type_error_message(
                span,
                |actual| {
                    format!("type `{}` does not implement any \
                             method in scope named `{}`",
                            actual,
                            method_ustring)
                },
                rcvr_ty,
                None);

            // If the method has the name of a field, give a help note
            if is_field {
                cx.sess.span_note(span,
                    format!("use `(s.{0})(...)` if you meant to call the \
                            function stored in the `{0}` field", method_ustring).as_slice());
            }

            if static_sources.len() > 0 {
                fcx.tcx().sess.fileline_note(
                    span,
                    "found defined static methods, maybe a `self` is missing?");

                report_candidates(fcx, span, method_name, static_sources);
            }
        }

        Ambiguity(sources) => {
            span_err!(fcx.sess(), span, E0034,
                      "multiple applicable methods in scope");

            report_candidates(fcx, span, method_name, sources);
        }
    }

    fn report_candidates(fcx: &FnCtxt,
                         span: Span,
                         method_name: ast::Name,
                         mut sources: Vec<CandidateSource>) {
        sources.sort();
        sources.dedup();

        for (idx, source) in sources.iter().enumerate() {
            match *source {
                ImplSource(impl_did) => {
                    // Provide the best span we can. Use the method, if local to crate, else
                    // the impl, if local to crate (method may be defaulted), else the call site.
                    let method = impl_method(fcx.tcx(), impl_did, method_name).unwrap();
                    let impl_span = fcx.tcx().map.def_id_span(impl_did, span);
                    let method_span = fcx.tcx().map.def_id_span(method.def_id, impl_span);

                    let impl_ty = impl_self_ty(fcx, span, impl_did).ty;

                    let insertion = match impl_trait_ref(fcx.tcx(), impl_did) {
                        None => format!(""),
                        Some(trait_ref) => format!(" of the trait `{}`",
                                                   ty::item_path_str(fcx.tcx(),
                                                                     trait_ref.def_id)),
                    };

                    span_note!(fcx.sess(), method_span,
                               "candidate #{} is defined in an impl{} for the type `{}`",
                               idx + 1u,
                               insertion,
                               impl_ty.user_string(fcx.tcx()));
                }
                TraitSource(trait_did) => {
                    let (_, method) = trait_method(fcx.tcx(), trait_did, method_name).unwrap();
                    let method_span = fcx.tcx().map.def_id_span(method.def_id, span);
                    span_note!(fcx.sess(), method_span,
                               "candidate #{} is defined in the trait `{}`",
                               idx + 1u,
                               ty::item_path_str(fcx.tcx(), trait_did));
                }
            }
        }
    }
}

fn trait_method(tcx: &ty::ctxt,
                trait_def_id: ast::DefId,
                method_name: ast::Name)
                -> Option<(uint, Rc<ty::Method>)>
{
    /*!
     * Find method with name `method_name` defined in `trait_def_id` and return it,
     * along with its index (or `None`, if no such method).
     */

    let trait_items = ty::trait_items(tcx, trait_def_id);
    trait_items
        .iter()
        .enumerate()
        .find(|&(_, ref item)| item.name() == method_name)
        .and_then(|(idx, item)| item.as_opt_method().map(|m| (idx, m)))
}

fn impl_method(tcx: &ty::ctxt,
               impl_def_id: ast::DefId,
               method_name: ast::Name)
               -> Option<Rc<ty::Method>>
{
    let impl_items = tcx.impl_items.borrow();
    let impl_items = impl_items.find(&impl_def_id).unwrap();
    impl_items
        .iter()
        .map(|&did| ty::impl_or_trait_item(tcx, did.def_id()))
        .find(|m| m.name() == method_name)
        .and_then(|item| item.as_opt_method())
}

