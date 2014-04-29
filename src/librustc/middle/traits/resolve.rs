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

use super::{Obligation, Obligations};
use super::{Overflow, NotApplicable, MaybeApplicable, DefinitelyApplicable};
use super::{Resolution, ResolvedTo, ResolvedToUnimpl, ResolvedToOverflow};
use super::{ImplEvaluation};
use super::{ToImplEvaluation};
use super::{VtableOrigin, VtableOrigins};
use super::{Vtable, Builtin, VtableParam, VtablePath};
use super::{util};

use middle::subst::{Subst, Substs, ParamSpace, VecPerParamSpace,
                    TypeSpace, SelfSpace, FnSpace};
use middle::ty;
use middle::typeck::infer;
use middle::typeck::infer::InferCtxt;
use std::rc::Rc;
use syntax::ast;
use syntax::codemap::Span;
use util::ppaux::Repr;

pub struct ResolutionContext<'cx> {
    infcx: &'cx InferCtxt<'cx>,
    param_env: &'cx ty::ParameterEnvironment,
}

/**
 * This return type is used for some of the `evaluate` family of
 * functions. It indicates that we have determined how an obligation
 * can be discharged but have not actually gone about and *fulfilled*
 * the obligation yet. That final step, called confirming, is when the
 * type environment is actually modified.
 */
enum UnconfirmedVtableOrigin {
    UnconfirmedImpl(ast::DefId),
    UnconfirmedParam(VtableParam),
    UnconfirmedBuiltin,
}

impl<'cx> ResolutionContext<'cx> {
    pub fn new(infcx: &'cx InferCtxt<'cx>,
               param_env: &'cx ty::ParameterEnvironment)
               -> ResolutionContext<'cx> {
        ResolutionContext { infcx: infcx, param_env: param_env }
    }

    pub fn tcx(&self) -> &'cx ty::ctxt {
        self.infcx.tcx
    }

    ///////////////////////////////////////////////////////////////////////////
    // Resolution
    //
    // Resolving an obligation means finding out how it will be
    // satisfied. This can affect the surrounding inference
    // environment.
    //
    // Resolving consists of two phases:
    // - Evaluation: test whether various impls etc apply
    // - Confirmation: assuming exactly one suitable resolution is
    //   found, that resolution is confirmed.

    fn try_resolve_all_obligations(&self,
                                   obligations: &Obligations)
                                   -> Option<Resolution<VtableOrigins>>
    {
        /*!
         * Attempts to resolve many obligations transactionally. Only
         * if *all* of them can be resolved will we actually confirm
         * anything.
         */

        let resolutions = obligations.map(|o| self.evaluate_obligation(o));

        debug!("resolutions={}", resolutions.repr(self.tcx()));

        if resolutions.any(|r| r.to_impl_evaluation() == Overflow) {
            return Some(ResolvedToOverflow);
        }

        if resolutions.any(|r| r.to_impl_evaluation() == NotApplicable) {
            return Some(ResolvedToUnimpl);
        }

        if resolutions.any(|r| r.to_impl_evaluation() == MaybeApplicable) {
            return None;
        }

        let (u_tys, u_selfs, u_fns) = resolutions.split();
        let c_tys = self.confirm_many(obligations.get_vec(TypeSpace), u_tys);
        let c_selfs = self.confirm_many(obligations.get_vec(SelfSpace), u_selfs);
        let c_fns = self.confirm_many(obligations.get_vec(FnSpace), u_fns);
        Some(ResolvedTo(VecPerParamSpace::new(c_tys, c_selfs, c_fns)))
    }

    pub fn try_resolve_obligation(&self,
                                  obligation: &Obligation)
                                  -> Option<Resolution<VtableOrigin>>
    {
        /*!
         * Determines whether the obligation can be satisfied. If it
         * can, returns a vtable indicating how it was satisfied. If
         * resolution is successful, this may cause side-effects in
         * the inference context, such as unifying type variables.
         */

        debug!("try_resolve_obligation(obligation={})",
               obligation.repr(self.tcx()));

        match self.evaluate_obligation(obligation) {
            None => None,
            Some(ResolvedToUnimpl) => Some(ResolvedToUnimpl),
            Some(ResolvedToOverflow) => Some(ResolvedToOverflow),
            Some(ResolvedTo(unconfirmed)) => {
                Some(ResolvedTo(self.confirm_vtable_origin(obligation,
                                                           unconfirmed)))
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Evaluation
    //
    // In general, evaluation is used to test whether an obligation
    // can be satisfied, either in general or via some specific
    // means. No evaluate function should have side-effects on its
    // surrounding environment: it is simply a test. This last point
    // is important because we need to detect ambiguity where multiple
    // impls or traits could apply, and so we need a way to test
    // whether something applies without "biasing" later tests due to
    // unintentional unification.

    pub fn evaluate_obligation(&self,
                               obligation: &Obligation)
                               -> Option<Resolution<UnconfirmedVtableOrigin>>
    {
        /*!
         * Evaluates whether the obligation can be satisfied. Returns
         * an indication of whether the obligation can be satisfied
         * and, if so, by what means. Never affects surrounding typing
         * environment.
         */

        debug!("evaluate_obligation({})", obligation.repr(self.tcx()));

        // Check for overflow.

        if obligation.recursion_depth >= 22 { // FIXME
            debug!("{} --> overflow", obligation.repr(self.tcx()));
            return Some(ResolvedToOverflow);
        }

        // Builtin bounds. Leverage TypeContents machinery.

        match self.tcx().lang_items.to_builtin_kind(obligation.trait_ref.def_id) {
            None => { }
            Some(bound) => {
                return self.evaluate_builtin_bound(obligation, bound);
            }
        }

        // Type parameters. Consider declared bounds. Stop if we find something.

        match self.evaluate_obligation_against_caller_bounds(obligation) {
            Some(r) => { return Some(r); }
            None => { }
        }

        // General case. Trawl through the impls.

        let impls = self.all_impls(obligation.trait_ref.def_id);

        if impls.len() == 0 {
            // Annoying edge case: if there are no impls, then there
            // is no way that this trait reference is implemented,
            // *unless* it contains unbound variables. In that case,
            // it is possible that one of those unbound variables will
            // be bound to a new type from some other crate which will
            // also contain impls.
            let trait_ref = obligation.trait_ref.clone();
            return if !self.trait_ref_contains_unconstrained_type_vars(&*trait_ref) {
                debug!("{} --> 0 matches, unimpl", obligation.repr(self.tcx()));
                Some(ResolvedToUnimpl)
            } else {
                debug!("{} --> 0 matches, ambig", obligation.repr(self.tcx()));
                None
            };
        }

        let evals = self.evaluate_impls(impls.as_slice(),
                                        obligation.span,
                                        obligation.recursion_depth,
                                        obligation.trait_ref.clone());

        if evals.contains(&Overflow) {
            // At least one of those impls may or may not be applicable.
            return Some(ResolvedToOverflow);
        }

        let matching = evals.iter()
                            .filter(|r| r.potentially_applicable())
                            .count();

        if matching == 0 {
            debug!("{} --> unimpl", obligation.repr(self.tcx()));
            return Some(ResolvedToUnimpl);
        }

        if matching > 1 {
            // Ambiguity. Either coherence failure will result or else
            // we don't know enough about types.
            debug!("{} --> ambig ({} cases)",
                   obligation.repr(self.tcx()),
                   matching);
            return None;
        }

        match evals.as_slice().position_elem(&DefinitelyApplicable) {
            None => {
                // One match, but it is not definitely applicable.
                return None;
            }

            Some(i) => {
                // One match, definitely applicable.
                debug!("{} --> 1 match", obligation.repr(self.tcx()));
                return Some(ResolvedTo(UnconfirmedImpl(*impls.get(i))));
            }
        }
    }

    fn evaluate_builtin_bound(&self,
                              obligation: &Obligation,
                              bound: ty::BuiltinBound)
                              -> Option<Resolution<UnconfirmedVtableOrigin>>
    {
        debug!("evaluate_builtin_bound(obligation={}, bound={})",
               obligation.repr(self.tcx()),
               bound.repr(self.tcx()));

        // If type is not fully resolved, we will not be able to
        // determine if the trait bound is met.
        //
        // FIXME -- This is overly conservative. For example, &T is
        // always copy, for all T.
        let t = match self.fully_resolved_self_type(&*obligation.trait_ref) {
            Some(t) => t,
            None => {
                debug!("{} --> builtin, inference, ambig",
                       obligation.repr(self.tcx()));
                return None;
            }
        };

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
        return Some(if met {
            ResolvedTo(UnconfirmedBuiltin)
        } else {
            ResolvedToUnimpl
        });
    }

    fn evaluate_obligation_against_caller_bounds(
        &self,
        obligation: &Obligation)
        -> Option<Resolution<UnconfirmedVtableOrigin>>
    {
        /*!
         * Given an obligation like `<SomeTrait for T>`, search the obligations
         * that the caller supplied to find out whether it is listed among
         * them.
         *
         * Never affects inference environment.
         */

        debug!("evaluate_obligation_against_caller_bounds({})",
               obligation.repr(self.tcx()));

        let obligation_self_ty = obligation.self_ty();
        for &space in ParamSpace::all().iter() {
            for (i, caller_obligation) in self.param_env.caller_obligations
                                                        .get_vec(space)
                                                        .iter()
                                                        .enumerate()
            {
                debug!("space={} i={} caller_obligation={}",
                       space, i, caller_obligation.repr(self.tcx()));

                // Skip over obligations that don't apply to
                // `self_ty`.
                let caller_bound = &caller_obligation.trait_ref;
                let caller_self_ty = caller_bound.substs.self_ty().unwrap();
                let r =
                    self.infcx.probe(
                        || self.match_self_types(obligation.span,
                                                 caller_self_ty,
                                                 obligation_self_ty));
                if r.is_err() {
                    continue;
                }

                // Does the bound match directly?
                let caller_bound = (*caller_bound).clone();
                if caller_bound.def_id == obligation.trait_ref.def_id {
                    let vtable_path =
                        VtablePath { space: space,
                                     obligation: i,
                                     supertraits: Vec::new() };
                    let vtable_param =
                        VtableParam { path: vtable_path,
                                      bound: caller_bound };
                    return Some(ResolvedTo(UnconfirmedParam(vtable_param)));
                }

                // If not, consider supertraits of the bound.
                let mut iter = self.supertraits(caller_bound);
                loop {
                    // FIXME(NDM) for loop expansion holds a ref too long
                    let superbound = match iter.next() {
                        Some(s) => s,
                        None => break
                    };

                    debug!("superbound = {}", superbound.repr(self.tcx()));

                    if superbound.def_id == obligation.trait_ref.def_id {
                        let supertraits = iter.indices();
                        let vtable_path =
                            VtablePath { space: space,
                                         obligation: i,
                                         supertraits: supertraits };
                        let vtable_param =
                            VtableParam { path: vtable_path,
                                          bound: superbound };
                        return Some(ResolvedTo(UnconfirmedParam(vtable_param)));
                    }
                }
            }
        }

        return None;
    }

    fn evaluate_impls(&self,
                      impl_def_ids: &[ast::DefId],
                      span: Span,
                      recursion_depth: uint,
                      trait_ref: Rc<ty::TraitRef>)
                      -> Vec<ImplEvaluation>
    {
        /*!
         * Evaluates whether each of the impls in `impl_def_ids`
         * can be used to satisfy `trait_ref`. See `evaluate_impl()`.
         */

        let self_ty = trait_ref.substs.self_ty().unwrap();
        impl_def_ids
            .iter()
            .map(|&impl_def_id| self.evaluate_impl(impl_def_id, span,
                                                   recursion_depth, self_ty))
            .collect()
    }

    pub fn evaluate_impl(&self,
                         impl_def_id: ast::DefId,
                         span: Span,
                         recursion_depth: uint,
                         self_ty: ty::t)
                         -> ImplEvaluation
    {
        /*!
         * Evaluates whether `impl_def_id` can be used to satisfy
         * `trait_ref`.  This is a "pure" evaluation and hence does
         * not affect any external state (e.g., no type variables are
         * unified, no other obligations are resolved, etc).
         */

        debug!("evaluate_impl({}, {}, {})",
               impl_def_id.repr(self.tcx()),
               recursion_depth,
               self_ty.repr(self.tcx()));

        self.infcx.probe(|| {
            let resolution = match self.match_impl(impl_def_id,
                                                   span,
                                                   recursion_depth,
                                                   self_ty) {
                Some(r) => r,
                None => {
                    // No result here means that we couldn't find a
                    // resolution yet.
                    return MaybeApplicable;
                }
            };

            debug!("evaluate_impl({}, {}) --> {}",
                   impl_def_id.repr(self.tcx()),
                   recursion_depth,
                   resolution.to_impl_evaluation());

            resolution.to_impl_evaluation()
        })
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

    pub fn match_impl(&self,
                      impl_def_id: ast::DefId,
                      span: Span,
                      recursion_depth: uint,
                      obligation_self_ty: ty::t)
                      -> Option<Resolution<Vtable>>
    {
        /*!
         * Given an impl `impl_def_id` for some trait T, tests whether
         * the impl can be applied to the self type `self_ty`. This
         * first checks the self type of the impl itself to make sure
         * it is a match, and then proceeds to check any nested
         * obligations the impl may impose.
         *
         * Returns `None` if we cannot yet determine whether the impl
         * is a match (this can occur if types are not fully known).
         * Otherwise, returns `Some(r)` with the resolution `r` (which
         * may or may not be successful).
         */

        // Check that the vtable the impl provides is of compatible
        // type with the vtable the obligation requires.
        let impl_substs = match self.match_impl_self_types(impl_def_id,
                                                           span,
                                                           obligation_self_ty) {
            Ok(s) => s,
            Err(_) => {
                // An error here means the types are just plain incompatible.
                return Some(ResolvedToUnimpl);
            }
        };

        // Check that the nested obligations the impl requires can be met.
        self.match_nested_obligations(impl_def_id,
                                      impl_substs,
                                      span,
                                      recursion_depth)
    }

    fn match_impl_self_types(&self,
                             impl_def_id: ast::DefId,
                             span: Span,
                             obligation_self_ty: ty::t)
                             -> Result<Substs, ty::type_err>
    {
        /*!
         * Determines whether the self type declared against
         * `impl_def_id` matches `obligation_self_ty`. If successful, returns the
         * substitutions used to make them match. See `match_impl()`.
         * For example, if `impl_def_id` is declared as:
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

        debug!("match_self_types(obligation_self_ty={}, impl_self_ty={})",
               obligation_self_ty.repr(self.tcx()),
               impl_self_ty.repr(self.tcx()));

        let () =
            try!(self.match_self_types(span, impl_self_ty, obligation_self_ty));

        Ok(impl_substs)
    }

    fn match_self_types(&self,
                        span: Span,
                        provided_self_ty: ty::t,
                        required_self_ty: ty::t)
                        -> Result<(),ty::type_err>
    {
        // FIXME(#5781) -- equating the types is stronger than
        // necessary. Should consider variance of trait w/r/t Self.

        let origin = infer::RelateSelfType(span);
        self.infcx.eq_types(false,
                            origin,
                            provided_self_ty,
                            required_self_ty)
    }

    fn match_nested_obligations(&self,
                                impl_def_id: ast::DefId,
                                impl_substs: Substs,
                                span: Span,
                                recursion_depth: uint)
                                -> Option<Resolution<Vtable>>
    {
        /*!
         * Determines whether the nested obligations specified on the
         * impl `impl_def_id` can be met when using the substitutions
         * `impl_substs`. For example, if `impl_def_id` is declared
         * as:
         *
         *    impl<T:Copy> Foo for ~T { ... }
         *
         * and `impl_substs` says that `T=int`, this method should
         * succeed. If `impl_substs` says `T=~int`, then it should
         * fail.  If `impl_substs` says `T=$0` where `$0` is some
         * unknown inference variable, then it neither succeeds nor
         * fails, because insufficient information is available to
         * decide. Returns `None` to indicate neither success nor
         * failure, and otherwise returns a complete resolution.
         */

        // Now check whether we can satisfy any obligations that the
        // impl itself requires. For example:
        //
        //     impl<T:Foo> Bar for T { ... }
        //
        // At this point, we've matched `Bar for T` against our
        // obligation -- let's say it's `Bar for uint` -- and hence we
        // know that `T=uint`.  But now we must check that `uint:Foo`.
        let impl_generics = ty::lookup_item_type(self.tcx(),
                                                 impl_def_id).generics;
        let obligations = self.impl_obligations(span,
                                                recursion_depth + 1,
                                                &impl_generics,
                                                &impl_substs);

        // We can only say that this obligation is correctly
        // satisfied if *all* nested obligations are satisfied.
        //
        // It'd be nice to have a more lenient rule, but unfortunately
        // we cannot if we want to maintain *crate concatenability*.
        // See the doc.rs section for details.

        match self.try_resolve_all_obligations(&obligations) {
            None => None,
            Some(ResolvedToUnimpl) => Some(ResolvedToUnimpl),
            Some(ResolvedToOverflow) => Some(ResolvedToOverflow),
            Some(ResolvedTo(origins)) => {
                let vtable = Vtable {
                    impl_def_id: impl_def_id,
                    substs: impl_substs,
                    origins: origins,
                };

                Some(ResolvedTo(vtable))
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // Confirmation
    //
    // The final step of resolution: once we know how an obligation is
    // is resolved, we confirm that resolution in order to have side-effects
    // on the typing environment.

    fn confirm_vtable_origin(&self,
                             obligation: &Obligation,
                             unconfirmed_origin: UnconfirmedVtableOrigin)
                             -> VtableOrigin
    {
        /*!
         * Given an unconfirmed resolution, "confirm it", which means
         * to perform the final unification. This may affect
         * surrounding typing environment.
         */

        debug!("confirm_vtable_origin(obligation={}, \
                                      unconfirmed_origin={})",
               obligation.repr(self.tcx()),
               unconfirmed_origin.repr(self.tcx()));

        match unconfirmed_origin {
            UnconfirmedBuiltin => {
                Builtin
            }
            UnconfirmedParam(param) => {
                let opt_error = self.confirm(obligation.span,
                                             obligation.trait_ref.clone(),
                                             param.bound.clone());
                VtableParam(param, opt_error)
            }
            UnconfirmedImpl(impl_def_id) => {
                self.confirm_obligation_against_impl(impl_def_id, obligation)
            }
        }
    }

    fn confirm_obligation_against_impl(&self,
                                       impl_def_id: ast::DefId,
                                       obligation: &Obligation)
                                       -> VtableOrigin
    {
        debug!("confirm_obligation_against_impl({}, {})",
               impl_def_id.repr(self.tcx()),
               obligation.repr(self.tcx()));

        let r = {
            match self.match_impl(impl_def_id,
                                  obligation.span,
                                  obligation.recursion_depth,
                                  obligation.trait_ref.self_ty()) {
                Some(r) => r,
                None => {
                    self.tcx().sess.bug(
                        format!("Impl {} was evaluatable against {} but \
                                     now is not",
                                impl_def_id.repr(self.tcx()),
                                obligation.trait_ref.repr(self.tcx()))
                            .as_slice());
                }
            }
        };

        match r {
            ResolvedTo(vtable) => {
                // We expect the impl to sucessfully resolve, which
                // yields a vtable. We must now "confirm" that vtable
                // and return it.

                let opt_error = self.confirm_vtable(obligation.span,
                                                    obligation.trait_ref.clone(),
                                                    &vtable);

                Vtable(vtable, opt_error)
            }
            ResolvedToOverflow | ResolvedToUnimpl => {
                self.tcx().sess.span_bug(
                    obligation.span,
                    format!("Impl {} was evaluatable against {} but \
                             now yields {}",
                            impl_def_id.repr(self.tcx()),
                            obligation.trait_ref.repr(self.tcx()),
                            r).as_slice());
            }
        }
    }

    fn confirm_vtable(&self,
                      obligation_span: Span,
                      obligation_trait_ref: Rc<ty::TraitRef>,
                      vtable: &Vtable)
                      -> Option<ty::type_err>
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
                                                vtable.impl_def_id).unwrap();
        let impl_trait_ref = impl_trait_ref.subst(self.tcx(),
                                                  &vtable.substs);
        self.confirm(obligation_span, obligation_trait_ref, impl_trait_ref)
    }

    fn confirm_many(&self,
                    obligations: &Vec<Obligation>,
                    resolutions: Vec<Option<Resolution<UnconfirmedVtableOrigin>>>)
                    -> Vec<VtableOrigin>
    {
        resolutions
            .move_iter()
            .map(|r| self.unwrap_successful_resolution(r))
            .zip(obligations.iter())
            .map(|(u_v_o, oblig)| self.confirm_vtable_origin(oblig, u_v_o))
            .collect()
    }

    fn unwrap_successful_resolution<R>(&self,
                                       resolution: Option<Resolution<R>>)
                                       -> R
    {
        match resolution {
            Some(ResolvedTo(v)) => v,
            _ => self.tcx().sess.bug("Expected successful resolutions")
        }
    }

    fn confirm(&self,
               obligation_span: Span,
               obligation_trait_ref: Rc<ty::TraitRef>,
               expected_trait_ref: Rc<ty::TraitRef>)
               -> Option<ty::type_err>
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
        match self.infcx.sub_trait_refs(false,
                                        origin,
                                        expected_trait_ref,
                                        obligation_trait_ref) {
            Ok(()) => None,
            Err(terr) => Some(terr),
        }
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

    fn trait_ref_contains_unconstrained_type_vars(&self,
                                                  trait_ref: &ty::TraitRef)
                                                  -> bool {
        self.fully_resolved_self_type(trait_ref).is_none()
    }

    fn fully_resolved_self_type(&self, trait_ref: &ty::TraitRef)
                                -> Option<ty::t>
    {
        let t = trait_ref.substs.self_ty().unwrap();
        let t = self.infcx.resolve_type_vars_if_possible(t);
        debug!("fully_resolved_self_type: {}", t.repr(self.tcx()));
        let mut found_infer = false;
        ty::walk_ty(t, |t| {
            match ty::get(t).sty {
                ty::ty_infer(_) => { found_infer = true; }
                _ => { }
            }
        });
        if found_infer { None } else { Some(t) }
    }

    fn supertraits(&self, trait_ref: Rc<ty::TraitRef>) -> util::Supertraits<'cx> {
        util::supertraits(self.tcx(), trait_ref)
    }

    fn impl_obligations(&self,
                        span: Span,
                        recursion_depth: uint,
                        impl_generics: &ty::Generics,
                        impl_substs: &Substs)
                        -> VecPerParamSpace<Obligation>
    {
        util::obligations(self.tcx(), span, recursion_depth,
                          impl_generics, impl_substs)
    }
}

impl<T> ToImplEvaluation for Option<Resolution<T>> {
    fn to_impl_evaluation(&self) -> ImplEvaluation {
        match *self {
            None => MaybeApplicable,
            Some(ref r) => r.to_impl_evaluation()
        }
    }
}

impl<T> ToImplEvaluation for Resolution<T> {
    fn to_impl_evaluation(&self) -> ImplEvaluation {
        match *self {
            ResolvedTo(_) => DefinitelyApplicable,
            ResolvedToUnimpl => NotApplicable,
            ResolvedToOverflow => Overflow,
        }
    }
}

impl Repr for UnconfirmedVtableOrigin {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        match *self {
            UnconfirmedImpl(def_id) =>
                format!("UnconfirmedImpl({})", def_id.repr(tcx)),
            UnconfirmedParam(ref param) =>
                format!("UnconfirmedParam({})",
                        param.repr(tcx)),
            UnconfirmedBuiltin =>
                format!("UnconfirmedBuiltin")
        }
    }
}
