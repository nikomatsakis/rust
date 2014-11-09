
// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::subst::{Subst, Substs};
use middle::typeck::infer::InferCtxt;
use middle::ty;
use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

use super::{ErrorReported, Obligation, ObligationCause, PredicateObligation,
            TraitObligation, VtableImpl, VtableParam, VtableParamData, VtableImplData};

///////////////////////////////////////////////////////////////////////////
// Elaboration iterator

pub struct Elaborator<'cx, 'tcx:'cx> {
    tcx: &'cx ty::ctxt<'tcx>,
    stack: Vec<StackEntry>,
    visited: HashSet<ty::Predicate>,
}

struct StackEntry {
    position: uint,
    predicates: Vec<ty::Predicate>,
}

pub fn elaborate_trait_ref<'cx, 'tcx>(
    tcx: &'cx ty::ctxt<'tcx>,
    trait_ref: Rc<ty::TraitRef>)
    -> Elaborator<'cx, 'tcx>
{
    elaborate_predicates(tcx, vec![ty::TraitPredicate(trait_ref)])
}

pub fn elaborate_trait_refs<'cx, 'tcx>(
    tcx: &'cx ty::ctxt<'tcx>,
    trait_refs: &[Rc<ty::TraitRef>])
    -> Elaborator<'cx, 'tcx>
{
    let predicates = trait_refs.iter()
                               .map(|trait_ref| ty::TraitPredicate((*trait_ref).clone()))
                               .collect();
    elaborate_predicates(tcx, predicates)
}

pub fn elaborate_predicates<'cx, 'tcx>(
    tcx: &'cx ty::ctxt<'tcx>,
    predicates: Vec<ty::Predicate>)
    -> Elaborator<'cx, 'tcx>
{
    let visited: HashSet<ty::Predicate> =
        predicates.iter()
                  .map(|b| (*b).clone())
                  .collect();

    let entry = StackEntry { position: 0, predicates: predicates };
    Elaborator { tcx: tcx, stack: vec![entry], visited: visited }
}

impl<'cx, 'tcx> Elaborator<'cx, 'tcx> {
    fn push(&mut self, predicate: &ty::Predicate) {
        match *predicate {
            ty::TraitPredicate(ref trait_ref) => {
                let mut predicates =
                    ty::predicates_for_trait_ref(self.tcx, &**trait_ref);

                // Only keep those bounds that we haven't already
                // seen.  This is necessary to prevent infinite
                // recursion in some cases.  One common case is when
                // people define `trait Sized { }` rather than `trait
                // Sized for Sized? { }`.
                predicates.retain(|r| self.visited.insert((*r).clone()));

                self.stack.push(StackEntry { position: 0,
                                             predicates: predicates });
            }
            ty::OutlivesPredicate(..) => {
                // Currently, we do not "elaborate" predicates like
                // `'a : 'b` or `T : 'a`.  We could conceivably do
                // more here.  For example,
                //
                //     &'a int : 'b
                //
                // implies that
                //
                //     'a : 'b
                //
                // and we could get even more if we took WF
                // constraints into account. For example,
                //
                //     &'a &'b int : 'c
                //
                // implies that
                //
                //     'b : 'a
                //     'a : 'c
            }
        }
    }
}

impl<'cx, 'tcx> Iterator<ty::Predicate> for Elaborator<'cx, 'tcx> {
    fn next(&mut self) -> Option<ty::Predicate> {
        loop {
            // Extract next item from top-most stack frame, if any.
            let next_predicate = match self.stack.last_mut() {
                None => {
                    // No more stack frames. Done.
                    return None;
                }
                Some(entry) => {
                    let p = entry.position;
                    if p < entry.predicates.len() {
                        // Still more predicates left in the top stack frame.
                        entry.position += 1;

                        let next_predicate =
                            entry.predicates[p].clone();

                        Some(next_predicate)
                    } else {
                        None
                    }
                }
            };

            match next_predicate {
                Some(next_predicate) => {
                    self.push(&next_predicate);
                    return Some(next_predicate);
                }

                None => {
                    // Top stack frame is exhausted, pop it.
                    self.stack.pop();
                }
            }
        }
    }
}


// determine the `self` type, using fresh variables for all variables
// declared on the impl declaration e.g., `impl<A,B> for ~[(A,B)]`
// would return ($0, $1) where $0 and $1 are freshly instantiated type
// variables.
pub fn fresh_substs_for_impl(infcx: &InferCtxt,
                             span: Span,
                             impl_def_id: ast::DefId)
                             -> Substs
{
    let tcx = infcx.tcx;
    let impl_generics = ty::lookup_item_type(tcx, impl_def_id).generics;
    infcx.fresh_substs_for_generics(span, &impl_generics)
}

impl<N> fmt::Show for VtableImplData<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VtableImpl({})", self.impl_def_id)
    }
}

impl fmt::Show for VtableParamData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VtableParam(...)")
    }
}

pub fn obligations_for_generics(tcx: &ty::ctxt,
                                cause: ObligationCause,
                                recursion_depth: uint,
                                generics: &ty::Generics,
                                substs: &Substs)
                                -> Vec<PredicateObligation>
{
    /*! See `super::obligations_for_generics` */

    debug!("obligations_for_generics(generics={}, substs={})",
           generics.repr(tcx), substs.repr(tcx));

    generics.predicates.iter()
        .map(|predicate| Obligation { cause: cause,
                                      recursion_depth: recursion_depth,
                                      predicate: predicate.subst(tcx, substs) })
        .collect()
}

pub fn trait_ref_for_builtin_bound(
    tcx: &ty::ctxt,
    builtin_bound: ty::BuiltinBound,
    param_ty: ty::t)
    -> Option<Rc<ty::TraitRef>>
{
    match tcx.lang_items.from_builtin_kind(builtin_bound) {
        Ok(def_id) => {
            Some(Rc::new(ty::TraitRef {
                def_id: def_id,
                substs: Substs::empty().with_self_ty(param_ty)
            }))
        }
        Err(e) => {
            tcx.sess.err(e.as_slice());
            None
        }
    }
}

pub fn builtin_bound_for_trait_ref(
    tcx: &ty::ctxt,
    trait_ref: &ty::TraitRef)
    -> Option<ty::BuiltinBound>
{
  tcx.lang_items.to_builtin_kind(trait_ref.def_id)
}

pub fn obligation_for_builtin_bound(
    tcx: &ty::ctxt,
    cause: ObligationCause,
    builtin_bound: ty::BuiltinBound,
    recursion_depth: uint,
    param_ty: ty::t)
    -> Result<TraitObligation, ErrorReported>
{
    let trait_ref = trait_ref_for_builtin_bound(tcx, builtin_bound, param_ty);
    match trait_ref {
        Some(trait_ref) => Ok(Obligation {
                cause: cause,
                recursion_depth: recursion_depth,
                predicate: trait_ref
            }),
        None => Err(ErrorReported)
    }
}

impl<P:Repr> Repr for super::Obligation<P> {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("Obligation(predicate={},depth={})",
                self.predicate.repr(tcx),
                self.recursion_depth)
    }
}

impl<N:Repr> Repr for super::Vtable<N> {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            super::VtableImpl(ref v) =>
                v.repr(tcx),

            super::VtableUnboxedClosure(ref d) =>
                format!("VtableUnboxedClosure({})",
                        d.repr(tcx)),

            super::VtableParam(ref v) =>
                format!("VtableParam({})", v.repr(tcx)),

            super::VtableBuiltin(ref d) =>
                d.repr(tcx)
        }
    }
}

impl<N:Repr> Repr for super::VtableImplData<N> {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("VtableImpl(impl_def_id={}, substs={}, nested={})",
                self.impl_def_id.repr(tcx),
                self.substs.repr(tcx),
                self.nested.repr(tcx))
    }
}

impl<N:Repr> Repr for super::VtableBuiltinData<N> {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("VtableBuiltin(nested={})",
                self.nested.repr(tcx))
    }
}

impl Repr for super::VtableParamData {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("VtableParam(bound={})",
                self.bound.repr(tcx))
    }
}

impl Repr for super::SelectionError {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            super::Overflow =>
                format!("Overflow"),

            super::Unimplemented =>
                format!("Unimplemented"),

            super::OutputTypeParameterMismatch(ref t, ref e) =>
                format!("OutputTypeParameterMismatch({}, {})",
                        t.repr(tcx),
                        e.repr(tcx)),
        }
    }
}

impl Repr for super::FulfillmentError {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("FulfillmentError({},{})",
                self.obligation.repr(tcx),
                self.code.repr(tcx))
    }
}

impl Repr for super::FulfillmentErrorCode {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            super::CodeSelectionError(ref o) => o.repr(tcx),
            super::CodeAmbiguity => format!("Ambiguity")
        }
    }
}

impl fmt::Show for super::FulfillmentErrorCode {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            super::CodeSelectionError(ref e) => write!(f, "{}", e),
            super::CodeAmbiguity => write!(f, "Ambiguity")
        }
    }
}

impl Repr for ty::type_err {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        ty::type_err_to_str(tcx, self)
    }
}
