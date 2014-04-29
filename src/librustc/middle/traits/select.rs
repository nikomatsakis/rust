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

use super::{Obligation};
use super::{EvaluationResult, EvaluatedToMatch,
            EvaluatedToAmbiguity, EvaluatedToUnmatch};
use super::{SelectionError, Unimplemented, Overflow,
            OutputTypeParameterMismatch};
use super::{Selection};
use super::{SelectionResult};
use super::{VtableBuiltin, VtableImpl, VtableParam};
use super::{util};

use middle::subst::{Subst, Substs, ParamSpace, VecPerParamSpace};
use middle::ty;
use middle::typeck::infer;
use middle::typeck::infer::InferCtxt;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

pub struct SelectionContext<'cx> {
    infcx: &'cx InferCtxt<'cx>,
    param_env: &'cx ty::ParameterEnvironment,
}

enum MatchResult<T> {
    Matched(T),
    AmbiguousMatch,
    NoMatch
}

enum Candidate {
    MatchedBuiltinCandidate,
    AmbiguousBuiltinCandidate,
    MatchedParamCandidate(VtableParam),
    AmbiguousParamCandidate,
    Impl(ImplCandidate)
}

enum ImplCandidate {
    MatchedImplCandidate(ast::DefId),
    AmbiguousImplCandidate(ast::DefId),
}

impl<'cx> SelectionContext<'cx> {
    pub fn new(infcx: &'cx InferCtxt<'cx>,
               param_env: &'cx ty::ParameterEnvironment)
               -> SelectionContext<'cx> {
        SelectionContext { infcx: infcx, param_env: param_env }
    }

    pub fn tcx(&self) -> &'cx ty::ctxt {
        self.infcx.tcx
    }

    ///////////////////////////////////////////////////////////////////////////
    // Selection
    //
    // The selection phase tries to identify *how* an obligation will
    // be resolved. For example, it will identify which impl or
    // parameter bound is to be used. The process can be inconclusive
    // if the self type in the obligation is not fully inferred. Selection
    // can result in an error in one of two ways:
    //
    // 1. If no applicable impl or parameter bound can be found.
    // 2. If the output type parameters in the obligation do not match
    //    those specified by the impl/bound. For example, if the obligation
    //    is `Vec<Foo>:Iterable<Bar>`, but the impl specifies
    //    `impl<T> Iterable<T> for Vec<T>`, than an error would result.

    pub fn select(&self, obligation: &Obligation) -> SelectionResult<Selection> {
        /*!
         * Evaluates whether the obligation can be satisfied. Returns
         * an indication of whether the obligation can be satisfied
         * and, if so, by what means. Never affects surrounding typing
         * environment.
         */

        debug!("select({})", obligation.repr(self.tcx()));

        match try!(self.candidate_from_obligation(obligation)) {
            None => Ok(None),
            Some(candidate) => self.confirm_candidate(obligation, candidate),
        }
    }

    pub fn select_inherent_impl(&self,
                                impl_def_id: ast::DefId,
                                obligation_span: Span,
                                obligation_self_ty: ty::t)
                                -> SelectionResult<VtableImpl<Obligation>>
    {
        debug!("select_inherent_impl(impl_def_id={}, obligation_self_ty={})",
               impl_def_id.repr(self.tcx()),
               obligation_self_ty.repr(self.tcx()));

        match self.candidate_from_impl(impl_def_id,
                                       obligation_span,
                                       obligation_self_ty) {
            Some(MatchedImplCandidate(impl_def_id)) => {
                let vtable_impl =
                    try!(self.confirm_inherent_impl_candidate(
                        impl_def_id,
                        obligation_span,
                        obligation_self_ty,
                        0));
                Ok(Some(vtable_impl))
            }
            Some(AmbiguousImplCandidate(_)) => {
                Ok(None)
            }
            None => {
                Err(Unimplemented)
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // EVALUATION

    pub fn evaluate_obligation(&self,
                               obligation: &Obligation)
                               -> EvaluationResult
    {
        /*!
         * Evaluates whether the obligation `obligation` can be
         * satisfied (by any means).
         */

        debug!("evaluate_obligation({})",
               obligation.repr(self.tcx()));

        match self.candidate_from_obligation(obligation) {
            Ok(Some(c)) => c.to_evaluation_result(),
            Ok(None) => EvaluatedToAmbiguity,
            Err(_) => EvaluatedToUnmatch,
        }
    }

    pub fn evaluate_impl(&self,
                         impl_def_id: ast::DefId,
                         obligation_span: Span,
                         obligation_self_ty: ty::t)
                         -> EvaluationResult
    {
        /*!
         * Evaluates whether the impl with id `impl_def_id` could be
         * applied to the self type `obligation_self_ty`. This can be
         * used either for trait or inherent impls.
         */

        debug!("evaluate_impl(impl_def_id={}, obligation_self_ty={})",
               impl_def_id.repr(self.tcx()),
               obligation_self_ty.repr(self.tcx()));

        match self.candidate_from_impl(impl_def_id,
                                       obligation_span,
                                       obligation_self_ty) {
            Some(c) => c.to_evaluation_result(),
            None => EvaluatedToUnmatch,
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // CANDIDATE ASSEMBLY

    fn candidate_from_obligation(&self, obligation: &Obligation)
                                 -> SelectionResult<Candidate>
    {
        debug!("candidate_from_obligation({})",
               obligation.repr(self.tcx()));

        let mut candidates = try!(self.assemble_candidates(obligation));

        debug!("candidate_from_obligation: {} candidates for {}",
               candidates.len(), obligation.repr(self.tcx()));

        // Examine candidates to determine outcome. Ideally we will
        // have exactly one candidate that is definitively applicable.

        if candidates.len() == 0 {
            // Annoying edge case: if there are no impls, then there
            // is no way that this trait reference is implemented,
            // *unless* it contains unbound variables. In that case,
            // it is possible that one of those unbound variables will
            // be bound to a new type from some other crate which will
            // also contain impls.
            let trait_ref = &*obligation.trait_ref;
            return if !self.trait_ref_unconstrained(trait_ref) {
                debug!("candidate_from_obligation({}) -> 0 matches, unimpl",
                       obligation.repr(self.tcx()));
                Err(Unimplemented)
            } else {
                debug!("candidate_from_obligation({}) -> 0 matches, ambig",
                       obligation.repr(self.tcx()));
                Ok(None)
            };
        }

        if candidates.len() > 1 {
            // Ambiguity. We really should report back more information
            // on the potential candidates.
            debug!("candidate_from_obligation({}) -> multiple matches, ambig",
                   obligation.repr(self.tcx()));

            return Ok(None);
        }

        Ok(candidates.pop())
    }

    fn assemble_candidates(&self, obligation: &Obligation)
                           -> Result<Vec<Candidate>, SelectionError>
    {
        // Check for overflow.

        let recursion_limit = self.infcx.tcx.sess.recursion_limit.get();
        if obligation.recursion_depth >= recursion_limit {
            debug!("{} --> overflow", obligation.repr(self.tcx()));
            return Err(Overflow);
        }

        let mut candidates = Vec::new();

        match self.tcx().lang_items.to_builtin_kind(obligation.trait_ref.def_id) {
            Some(bound) => {
                // Builtin bounds. Leverage TypeContents machinery.

                self.assemble_builtin_bound_candidates(obligation,
                                                       bound,
                                                       &mut candidates);
            }

            None => {
                // Other bounds. Consider both in-scope bounds from fn decl
                // and applicable impls.

                try!(self.assemble_candidates_from_caller_bounds(obligation,
                                                                 &mut candidates));
                try!(self.assemble_candidates_from_impls(obligation,
                                                         &mut candidates));
            }
        }

        Ok(candidates)
    }

    fn assemble_builtin_bound_candidates(&self,
                                         obligation: &Obligation,
                                         bound: ty::BuiltinBound,
                                         candidates: &mut Vec<Candidate>)
    {
        debug!("select_builtin_bound(obligation={}, bound={})",
               obligation.repr(self.tcx()),
               bound.repr(self.tcx()));

        let t = obligation.trait_ref.substs.self_ty().unwrap();
        let t = self.infcx.resolve_type_vars_if_possible(t);

        if ty::type_is_error(t) {
            debug!("{} --> self type is error",
                   obligation.repr(self.tcx()));
            return;
        }

        // Determine if builtin bound is met.
        let tc = ty::type_contents(self.tcx(), t);
        let met = match bound {
            ty::BoundStatic => tc.is_static(self.tcx()),
            ty::BoundSend   => tc.is_sendable(self.tcx()),
            ty::BoundSized  => tc.is_sized(self.tcx()),
            ty::BoundCopy   => tc.is_copy(self.tcx()),
            ty::BoundShare  => tc.is_sharable(self.tcx()),
        };

        debug!("{} --> builtin met={}", obligation.repr(self.tcx()), met);

        // Resolve the obligation one way or the other.
        if met {
            candidates.push(MatchedBuiltinCandidate);
        } else if ty::type_needs_infer(t) {
            // Type is not fully resolved, so we can't say for sure
            // whether it meets builtin bound. This is actually overly
            // conservative but ok for now. To properly fix we ought
            // to have better support for treating builtin kinds like
            // synthetic impls rather than leaning on the type
            // contents machinery.
            candidates.push(AmbiguousBuiltinCandidate);
        }
    }

    fn assemble_candidates_from_caller_bounds(&self,
                                              obligation: &Obligation,
                                              candidates: &mut Vec<Candidate>)
                                              -> Result<(),SelectionError>
    {
        /*!
         * Given an obligation like `<SomeTrait for T>`, search the obligations
         * that the caller supplied to find out whether it is listed among
         * them.
         *
         * Never affects inference environment.
         */

        debug!("select_from_caller_bounds({})",
               obligation.repr(self.tcx()));

        let skol_obligation_self_ty =
            infer::skolemize(self.infcx, obligation.self_ty());
        for &space in ParamSpace::all().iter() {
            for (i, caller_obligation) in self.param_env.caller_obligations
                                                        .get_slice(space)
                                                        .iter()
                                                        .enumerate()
            {
                debug!("space={} i={} caller_obligation={}",
                       space, i, caller_obligation.repr(self.tcx()));

                // Skip over obligations that don't apply to
                // `self_ty`.
                let caller_bound = &caller_obligation.trait_ref;
                let caller_self_ty = caller_bound.substs.self_ty().unwrap();
                match self.match_self_types(obligation.span,
                                            caller_self_ty,
                                            skol_obligation_self_ty) {
                    AmbiguousMatch => {
                        debug!("-> AmbiguousParamCandidate");
                        candidates.push(AmbiguousParamCandidate);
                        return Ok(()); // FIXME
                    }
                    NoMatch => {
                        continue;
                    }
                    Matched(()) => { }
                }

                // Search through the trait (and its supertraits) to
                // see if it matches the def-id we are looking for.
                let caller_bound = (*caller_bound).clone();
                match util::search_trait_and_supertraits_from_bound(
                    self.infcx.tcx, space, i, caller_bound,
                    |d| d == obligation.trait_ref.def_id)
                {
                    Some(vtable_param) => {
                        // If so, we're done!
                        debug!("-> MatchedParamCandidate({})", vtable_param);
                        candidates.push(MatchedParamCandidate(vtable_param));
                        return Ok(()); // FIXME
                    }

                    None => {
                    }
                }
            }
        }

        Ok(())
    }

    fn assemble_candidates_from_impls(&self,
                                      obligation: &Obligation,
                                      candidates: &mut Vec<Candidate>)
                                      -> Result<(), SelectionError>
    {
        let all_impls = self.all_impls(obligation.trait_ref.def_id);
        let obligation_self_ty = obligation.trait_ref.self_ty();
        for &impl_def_id in all_impls.iter() {
            self.infcx.probe(|| {
                match self.candidate_from_impl(impl_def_id,
                                               obligation.span,
                                               obligation_self_ty) {
                    Some(c) => {
                        candidates.push(Impl(c));
                    }

                    None => { }
                }
            });
        }
        Ok(())
    }

    fn candidate_from_impl(&self,
                           impl_def_id: ast::DefId,
                           obligation_span: Span,
                           obligation_self_ty: ty::t)
                           -> Option<ImplCandidate>
    {
        let skol_self_ty = infer::skolemize(self.infcx, obligation_self_ty);
        match self.match_impl_self_types(impl_def_id,
                                         obligation_span,
                                         skol_self_ty) {
            Matched(_) => {
                Some(MatchedImplCandidate(impl_def_id))
            }

            AmbiguousMatch => {
                Some(AmbiguousImplCandidate(impl_def_id))
            }

            NoMatch => {
                None
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // CONFIRMATION

    fn confirm_candidate(&self,
                         obligation: &Obligation,
                         candidate: Candidate)
                         -> SelectionResult<Selection>
    {
        debug!("confirm_candidate({}, {})",
               obligation.repr(self.tcx()),
               candidate.repr(self.tcx()));

        match candidate {
            AmbiguousBuiltinCandidate |
            AmbiguousParamCandidate |
            Impl(AmbiguousImplCandidate(_)) => {
                Ok(None)
            }

            MatchedBuiltinCandidate => {
                Ok(Some(VtableBuiltin))
            }

            MatchedParamCandidate(param) => {
                Ok(Some(VtableParam(
                    try!(self.confirm_param_candidate(obligation, param)))))
            }

            Impl(MatchedImplCandidate(impl_def_id)) => {
                let vtable_impl = try!(self.confirm_impl_candidate(obligation,
                                                                   impl_def_id));
                Ok(Some(VtableImpl(vtable_impl)))
            }
        }
    }

    fn confirm_param_candidate(&self,
                               obligation: &Obligation,
                               param: VtableParam)
                               -> Result<VtableParam,SelectionError>
    {
        debug!("confirm_param_candidate({},{})",
               obligation.repr(self.tcx()),
               param.repr(self.tcx()));

        match self.confirm(obligation.span,
                           obligation.trait_ref.clone(),
                           param.bound.clone()) {
            Ok(()) => Ok(param),
            Err(e) => Err(OutputTypeParameterMismatch(e)),
        }
    }

    fn confirm_impl_candidate(&self,
                              obligation: &Obligation,
                              impl_def_id: ast::DefId)
                              -> Result<VtableImpl<Obligation>,SelectionError>
    {
        debug!("confirm_impl_candidate({},{})",
               obligation.repr(self.tcx()),
               impl_def_id.repr(self.tcx()));

        // For a non-inhernet impl, we begin the same way as an
        // inherent impl, by matching the self-type and assembling
        // list of nested obligations.
        let vtable_impl =
            try!(self.confirm_inherent_impl_candidate(
                impl_def_id,
                obligation.span,
                obligation.trait_ref.self_ty(),
                obligation.recursion_depth));

        // But then we must also match the output types.
        match self.confirm_impl_vtable(impl_def_id,
                                       obligation.span,
                                       obligation.trait_ref.clone(),
                                       &vtable_impl.substs) {
            Ok(()) => Ok(vtable_impl),
            Err(e) => Err(OutputTypeParameterMismatch(e))
        }
    }

    fn confirm_inherent_impl_candidate(&self,
                                       impl_def_id: ast::DefId,
                                       obligation_span: Span,
                                       obligation_self_ty: ty::t,
                                       obligation_recursion_depth: uint)
                                       -> Result<VtableImpl<Obligation>,
                                                 SelectionError>
    {
        let substs = match self.match_impl_self_types(impl_def_id,
                                                      obligation_span,
                                                      obligation_self_ty) {
            Matched(substs) => substs,
            AmbiguousMatch | NoMatch => {
                self.tcx().sess.bug(
                    format!("Impl {} was matchable against {} but now is not",
                            impl_def_id.repr(self.tcx()),
                            obligation_self_ty.repr(self.tcx()))
                        .as_slice());
            }
        };

        let impl_obligations =
            self.impl_obligations(obligation_span,
                                  obligation_recursion_depth,
                                  impl_def_id,
                                  &substs);
        let vtable_impl = VtableImpl { impl_def_id: impl_def_id,
                                       substs: substs,
                                       nested: impl_obligations };

        Ok(vtable_impl)
    }

    ///////////////////////////////////////////////////////////////////////////
    // Matching
    //
    // Matching is a common path used for both evaluation and
    // confirmation.  It basically unifies types that appear in impls
    // and traits. This does affect the surrounding environment;
    // therefore, when used during evaluation, match routines must be
    // run inside of a `probe()` so that their side-effects are
    // contained.

    fn match_impl_self_types(&self,
                             impl_def_id: ast::DefId,
                             span: Span,
                             obligation_self_ty: ty::t)
                             -> MatchResult<Substs>
    {
        /*!
         * Determines whether the self type declared against
         * `impl_def_id` matches `obligation_self_ty`. If successful,
         * returns the substitutions used to make them match. See
         * `match_impl()`.  For example, if `impl_def_id` is declared
         * as:
         *
         *    impl<T:Copy> Foo for ~T { ... }
         *
         * and `obligation_self_ty` is `int`, we'd back an `Err(_)`
         * result. But if `obligation_self_ty` were `~int`, we'd get
         * back `Ok(T=int)`.
         */

        // Create fresh type variables for each type parameter declared
        // on the impl etc.
        let impl_substs = util::fresh_substs_for_impl(self.infcx, span,
                                                      impl_def_id);

        // Find the self type for the impl.
        let impl_self_ty = ty::lookup_item_type(self.tcx(), impl_def_id).ty;
        let impl_self_ty = impl_self_ty.subst(self.tcx(), &impl_substs);

        debug!("match_impl_self_types(obligation_self_ty={}, impl_self_ty={})",
               obligation_self_ty.repr(self.tcx()),
               impl_self_ty.repr(self.tcx()));

        match self.match_self_types(span,
                                    impl_self_ty,
                                    obligation_self_ty) {
            Matched(()) => {
                debug!("Matched impl_substs={}", impl_substs.repr(self.tcx()));
                Matched(impl_substs)
            }
            AmbiguousMatch => {
                debug!("AmbiguousMatch");
                AmbiguousMatch
            }
            NoMatch => {
                debug!("NoMatch");
                NoMatch
            }
        }
    }

    fn match_self_types(&self,
                        span: Span,

                        // The self type provided by the impl/caller-obligation:
                        provided_self_ty: ty::t,

                        // The self type the obligation is for:
                        required_self_ty: ty::t)
                        -> MatchResult<()>
    {
        // FIXME(#5781) -- equating the types is stronger than
        // necessary. Should consider variance of trait w/r/t Self.

        let origin = infer::RelateSelfType(span);
        match self.infcx.eq_types(false,
                                  origin,
                                  provided_self_ty,
                                  required_self_ty) {
            Ok(()) => Matched(()),
            Err(ty::terr_sorts(ty::expected_found{expected: t1, found: t2})) => {
                // This error occurs when there is an unresolved type
                // variable in the `required_self_ty` that was forced
                // to unify with a non-type-variable. That basically
                // means we don't know enough to say with certainty
                // whether there is a match or not -- it depends on
                // how that type variable is ultimately resolved.
                if ty::type_is_skolemized(t1) || ty::type_is_skolemized(t2) {
                    AmbiguousMatch
                } else {
                    NoMatch
                }
            }
            Err(_) => NoMatch,
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Confirmation
    //
    // The final step of selection: once we know how an obligation is
    // is resolved, we confirm that selection in order to have
    // side-effects on the typing environment. This step also unifies
    // the output type parameters from the obligation with those found
    // on the impl/bound, which may yield type errors.

    fn confirm_impl_vtable(&self,
                           impl_def_id: ast::DefId,
                           obligation_span: Span,
                           obligation_trait_ref: Rc<ty::TraitRef>,
                           substs: &Substs)
                           -> Result<(), ty::type_err>
    {
        /*!
         * Relates the output type parameters from an impl to the
         * trait.  This may lead to type errors. The confirmation step
         * is separated from the main match procedure because these
         * type errors do not cause us to select another impl.
         *
         * As an example, consider matching the obligation
         * `Iterator<char> for Elems<int>` using the following impl:
         *
         *    impl<T> Iterator<T> for Elems<T> { ... }
         *
         * The match phase will succeed with substitution `T=int`.
         * The confirm step will then try to unify `int` and `char`
         * and yield an error.
         */

        let impl_trait_ref = ty::impl_trait_ref(self.tcx(),
                                                impl_def_id).unwrap();
        let impl_trait_ref = impl_trait_ref.subst(self.tcx(),
                                                  substs);
        self.confirm(obligation_span, obligation_trait_ref, impl_trait_ref)
    }

    fn confirm(&self,
               obligation_span: Span,
               obligation_trait_ref: Rc<ty::TraitRef>,
               expected_trait_ref: Rc<ty::TraitRef>)
               -> Result<(), ty::type_err>
    {
        /*!
         * After we have determined which impl applies, and with what
         * substitutions, there is one last step. We have to go back
         * and relate the "output" type parameters from the obligation
         * to the types that are specified in the impl.
         *
         * For example, imagine we have:
         *
         *     impl<T> Iterator<T> for Vec<T> { ... }
         *
         * and our obligation is `Iterator<Foo> for Vec<int>` (note
         * the mismatch in the obligation types). Up until this step,
         * no error would be reported: the self type is `Vec<int>`,
         * and that matches `Vec<T>` with the substitution `T=int`.
         * At this stage, we could then go and check that the type
         * parameters to the `Iterator` trait match.
         * (In terms of the parameters, the `expected_trait_ref`
         * here would be `Iterator<int> for Vec<int>`, and the
         * `obligation_trait_ref` would be `Iterator<Foo> for Vec<int>`.
         *
         * Note that this checking occurs *after* the impl has
         * selected, because these output type parameters should not
         * affect the selection of the impl. Therefore, if there is a
         * mismatch, we report an error to the user.
         */

        let origin = infer::RelateOutputImplTypes(obligation_span);

        let obligation_trait_ref = obligation_trait_ref.clone();
        self.infcx.sub_trait_refs(false,
                                  origin,
                                  expected_trait_ref,
                                  obligation_trait_ref)
    }

    ///////////////////////////////////////////////////////////////////////////
    // Miscellany

    fn all_impls(&self, trait_def_id: ast::DefId) -> Vec<ast::DefId> {
        /*!
         * Returns se tof all impls for a given trait.
         */

        ty::populate_implementations_for_trait_if_necessary(self.tcx(),
                                                            trait_def_id);
        match self.tcx().trait_impls.borrow().find(&trait_def_id) {
            None => Vec::new(),
            Some(impls) => impls.borrow().clone()
        }
    }

    fn impl_obligations(&self,
                        span: Span,
                        recursion_depth: uint,
                        impl_def_id: ast::DefId,
                        impl_substs: &Substs)
                        -> VecPerParamSpace<Obligation>
    {
        let impl_generics = ty::lookup_item_type(self.tcx(),
                                                 impl_def_id).generics;
        util::obligations(self.tcx(), span, recursion_depth,
                          &impl_generics, impl_substs)
    }

    fn trait_ref_unconstrained(&self,
                               trait_ref: &ty::TraitRef)
                               -> bool
    {
        /*!
         * True if the self type of the trait-ref contains
         * unconstrained type variables.
         */

        let mut found_skol = false;

        // Skolemization replaces all unconstrained type vars with
        // a SkolemizedTy instance. Then we search to see if we
        // found any.
        let skol_ty = infer::skolemize(self.infcx, trait_ref.self_ty());
        ty::walk_ty(skol_ty, |t| {
            match ty::get(t).sty {
                ty::ty_infer(ty::SkolemizedTy(_)) => { found_skol = true; }
                _ => { }
            }
        });

        found_skol
    }
}

impl Candidate {
    fn to_evaluation_result(&self) -> EvaluationResult {
        match *self {
            Impl(ref i) => i.to_evaluation_result(),

            MatchedBuiltinCandidate | MatchedParamCandidate(..) => {
                EvaluatedToMatch
            }

            AmbiguousBuiltinCandidate | AmbiguousParamCandidate => {
                EvaluatedToAmbiguity
            }
        }
    }
}

impl ImplCandidate {
    fn to_evaluation_result(&self) -> EvaluationResult {
        match *self {
            MatchedImplCandidate(..) => EvaluatedToMatch,
            AmbiguousImplCandidate(..) => EvaluatedToAmbiguity
        }
    }
}

impl Repr for Candidate {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            MatchedBuiltinCandidate => format!("MatchedBuiltinCandidate"),
            AmbiguousBuiltinCandidate => format!("AmbiguousBuiltinCandidate"),
            MatchedParamCandidate(ref r) => format!("MatchedParamCandidate({})",
                                                    r.repr(tcx)),
            AmbiguousParamCandidate => format!("AmbiguousParamCandidate"),
            Impl(ref i) => i.repr(tcx)
        }
    }
}

impl Repr for ImplCandidate {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            MatchedImplCandidate(ref d) => format!("MatchedImplCandidate({})",
                                                   d.repr(tcx)),
            AmbiguousImplCandidate(ref d) => format!("AmbiguousImplCandidate({})",
                                                     d.repr(tcx)),
        }
    }
}

