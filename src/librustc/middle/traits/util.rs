// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::subst;
use middle::subst::{ParamSpace, Subst, Substs, VecPerParamSpace};
use middle::typeck::infer::InferCtxt;
use middle::ty;
use std::fmt;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

use super::{Obligation, VtableImpl, VtablePath, VtableParam};

///////////////////////////////////////////////////////////////////////////
// Supertrait iterator

pub struct Supertraits<'cx> {
    tcx: &'cx ty::ctxt,
    stack: Vec<SupertraitEntry>,
}

struct SupertraitEntry {
    trait_ref: Rc<ty::TraitRef>,
    position: uint,
    raw_supertraits: Rc<Vec<Rc<ty::TraitRef>>>,
}

pub fn supertraits<'cx>(tcx: &'cx ty::ctxt,
                        trait_ref: Rc<ty::TraitRef>)
                        -> Supertraits<'cx>
{
    let mut i = Supertraits { tcx: tcx, stack: Vec::new() };
    i.push(trait_ref);
    return i;
}

impl<'cx> Supertraits<'cx> {
    fn push(&mut self, trait_ref: Rc<ty::TraitRef>) {
        let raw_supertraits = ty::trait_supertraits(self.tcx, trait_ref.def_id);
        let entry = SupertraitEntry { trait_ref: trait_ref,
                                      position: 0,
                                      raw_supertraits: raw_supertraits };
        self.stack.push(entry);
    }

    pub fn indices(&self) -> Vec<uint> {
        /*!
         * Returns the path taken through the trait supertraits to
         * reach the current point.
         */

        self.stack.iter().map(|e| e.position).collect()
    }
}

impl<'cx> Iterator<Rc<ty::TraitRef>> for Supertraits<'cx> {
    fn next(&mut self) -> Option<Rc<ty::TraitRef>> {
        loop {
            // Extract next item from top-most stack frame, if any.
            let next_trait = match self.stack.mut_last() {
                None => {
                    // No more stack frames. Done.
                    return None;
                }
                Some(entry) => {
                    let p = entry.position;
                    if p < entry.raw_supertraits.len() {
                        // Still more supertraits left in the top stack frame.
                        entry.position += 1;

                        let raw_next_trait =
                            entry.raw_supertraits.get(p);
                        let next_trait =
                            (*raw_next_trait).subst(self.tcx,
                                                    &entry.trait_ref.substs);
                        Some(next_trait)
                    } else {
                        None
                    }
                }
            };

            match next_trait {
                Some(next_trait) => {
                    self.push(next_trait.clone());
                    return Some(next_trait);
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
    infcx.fresh_substs_for_type(span, &impl_generics)
}

impl<N> fmt::Show for VtableImpl<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VtableImpl({})", self.impl_def_id)
    }
}

impl fmt::Show for VtableParam {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "VtableParam({})", self.path)
    }
}

pub fn obligations(tcx: &ty::ctxt,
                   span: Span,
                   recursion_depth: uint,
                   generics: &ty::Generics,
                   substs: &Substs)
                   -> VecPerParamSpace<Obligation>
{
    /*!
     * Given generics for an impl like:
     *
     *    impl<A:Foo, B:Bar+Qux> ...
     *
     * and a substs vector like `<A=A0, B=B0>`, yields a result like
     *
     *    [[Foo for A0, Bar for B0, Qux for B0], [], []]
     */

    debug!("obligations(generics={}, substs={})",
           generics.repr(tcx), substs.repr(tcx));

    let mut obligations = VecPerParamSpace::empty();

    for &space in subst::ParamSpace::all().iter() {
        let defs = generics.types.get_slice(space);
        for def in defs.iter() {
            let param_ty = *substs.types.get(def.space, def.index);

            for builtin_bound in def.bounds.builtin_bounds.iter() {
                push_obligation_for_builtin_bound(tcx,
                                                  span,
                                                  builtin_bound,
                                                  recursion_depth,
                                                  param_ty,
                                                  space,
                                                  &mut obligations);
            }

            for bound_trait_ref in def.bounds.trait_bounds.iter() {
                let bound_trait_ref = bound_trait_ref.subst(tcx, substs);
                obligations.push(space, Obligation {
                    span: span,
                    recursion_depth: recursion_depth,
                    trait_ref: bound_trait_ref,
                });
            }
        }
    }

    debug!("obligations() ==> {}", obligations.repr(tcx));

    return obligations;

    fn push_obligation_for_builtin_bound(
        tcx: &ty::ctxt,
        span: Span,
        builtin_bound: ty::BuiltinBound,
        recursion_depth: uint,
        param_ty: ty::t,
        space: subst::ParamSpace,
        obligations: &mut VecPerParamSpace<Obligation>)
    {
        if builtin_bound != ty::BoundStatic {
            match tcx.lang_items.from_builtin_kind(builtin_bound) {
                Ok(def_id) => {
                    obligations.push(space, Obligation {
                        span: span,
                        recursion_depth: recursion_depth,
                        trait_ref: Rc::new(ty::TraitRef {
                            def_id: def_id,
                            substs: Substs::empty().with_self_ty(param_ty),
                        }),
                    });
                }
                Err(e) => {
                    tcx.sess.span_bug(span, e.as_slice());
                }
            }
        }
    }
}

pub fn search_trait_and_supertraits_from_bound(tcx: &ty::ctxt,
                                               space: ParamSpace,
                                               i: uint,
                                               caller_bound: Rc<ty::TraitRef>,
                                               test: |ast::DefId| -> bool)
                                               -> Option<VtableParam>
{
    /*!
     * Starting from a caller obligation `caller_bound` (which has
     * coordinates `space`/`i` in the list of caller obligations),
     * search through the trait and supertraits to find one where
     * `test(d)` is true, where `d` is the def-id of the
     * trait/supertrait.  If any is found, return `Some(p)` where `p`
     * is the path to that trait/supertrait. Else `None`.
     */

    // Does the bound match directly?
    if test(caller_bound.def_id) {
        let vtable_path =
            VtablePath { space: space,
                         obligation: i,
                         supertraits: Vec::new() };
        let vtable_param =
            VtableParam { path: vtable_path,
                          bound: caller_bound };
        return Some(vtable_param);
    }

    // If not, consider supertraits of the bound.
    let mut iter = supertraits(tcx, caller_bound.clone());
    loop {
        // FIXME(NDM) for loop expansion holds a ref too long
        let superbound = match iter.next() {
            Some(s) => s,
            None => break
        };

        debug!("superbound = {}", superbound.repr(tcx));

        if test(superbound.def_id) {
            let supertraits = iter.indices();
            let vtable_path =
                VtablePath { space: space,
                             obligation: i,
                             supertraits: supertraits };
            let vtable_param =
                VtableParam { path: vtable_path,
                              bound: superbound };
            return Some(vtable_param);
        }
    }

    return None;
}

impl Repr for super::Obligation {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("Obligation(trait_ref={},depth={})",
                self.trait_ref.repr(tcx),
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

            super::VtableBuiltin =>
                format!("Builtin"),
        }
    }
}

impl Repr for super::VtableOrigin {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        self.vtable.repr(tcx)
    }
}

impl<N:Repr> Repr for super::VtableImpl<N> {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("VtableImpl(impl_def_id={}, substs={}, nested={})",
                self.impl_def_id.repr(tcx),
                self.substs.repr(tcx),
                self.nested.repr(tcx))
    }
}

impl Repr for super::VtableParam {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("VtableParam(bound={}, path={})",
                self.bound.repr(tcx),
                self.path.repr(tcx))
    }
}

impl Repr for super::VtablePath {
    fn repr(&self, _tcx: &ty::ctxt) -> String {
        format!("VtablePath({}, {})", self.obligation, self.supertraits)
    }
}

impl Repr for super::SelectionError {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            super::Unimplemented =>
                format!("Unimplemented"),

            super::Overflow =>
                format!("Overflow"),

            super::OutputTypeParameterMismatch(ref e) =>
                format!("OutputTypeParameterMismatch({})", e.repr(tcx)),
        }
    }
}

impl<'o> Repr for super::FulfillmentError<'o> {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("FulfillmentError({},{})",
                self.obligation.repr(tcx),
                self.code.repr(tcx))
    }
}

impl Repr for super::FulfillmentErrorCode {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            super::SelectionError(ref o) => o.repr(tcx),
            super::Ambiguity => format!("Ambiguity")
        }
    }
}
