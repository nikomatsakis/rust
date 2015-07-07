// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::infer::InferCtxt;
use middle::ty::{self, RegionEscape, Ty, HasTypeFlags};
use middle::wf;

use std::collections::HashSet;
use std::fmt;
use syntax::ast;
use util::common::ErrorReported;
use util::nodemap::NodeMap;

use super::CodeAmbiguity;
use super::CodeProjectionError;
use super::CodeSelectionError;
use super::FulfillmentError;
use super::ObligationCause;
use super::PredicateObligation;
use super::project;
use super::select::SelectionContext;
use super::Unimplemented;
use super::util::predicate_for_builtin_bound;

pub struct FulfilledPredicates<'tcx> {
    set: HashSet<ty::Predicate<'tcx>>
}

/// The fulfillment context is used to drive trait resolution.  It
/// consists of a list of obligations that must be (eventually)
/// satisfied. The job is to track which are satisfied, which yielded
/// errors, and which are still pending. At any point, users can call
/// `select_where_possible`, and the fulfilment context will try to do
/// selection, retaining only those obligations that remain
/// ambiguous. This may be helpful in pushing type inference
/// along. Once all type inference constraints have been generated, the
/// method `select_all_or_error` can be used to report any remaining
/// ambiguous cases as errors.
pub struct FulfillmentContext<'tcx> {
    // a simple cache that aims to cache *exact duplicate obligations*
    // and avoid adding them twice. This serves a different purpose
    // than the `SelectionCache`: it avoids duplicate errors and
    // permits recursive obligations, which are often generated from
    // traits like `Send` et al.
    duplicate_set: FulfilledPredicates<'tcx>,

    // A list of all obligations that have been registered with this
    // fulfillment context.
    predicates: Vec<PredicateObligation<'tcx>>,

    // Remembers the count of trait obligations that we have already
    // attempted to select. This is used to avoid repeating work
    // when `select_new_obligations` is called.
    attempted_mark: usize,

    // A set of constraints that regionck must validate. Each
    // constraint has the form `T:'a`, meaning "some type `T` must
    // outlive the lifetime 'a". These constraints derive from
    // instantiated type parameters. So if you had a struct defined
    // like
    //
    //     struct Foo<T:'static> { ... }
    //
    // then in some expression `let x = Foo { ... }` it will
    // instantiate the type parameter `T` with a fresh type `$0`. At
    // the same time, it will record a region obligation of
    // `$0:'static`. This will get checked later by regionck. (We
    // can't generally check these things right away because we have
    // to wait until types are resolved.)
    //
    // These are stored in a map keyed to the id of the innermost
    // enclosing fn body / static initializer expression. This is
    // because the location where the obligation was incurred can be
    // relevant with respect to which sublifetime assumptions are in
    // place. The reason that we store under the fn-id, and not
    // something more fine-grained, is so that it is easier for
    // regionck to be sure that it has found *all* the region
    // obligations (otherwise, it's easy to fail to walk to a
    // particular node-id).
    region_obligations: NodeMap<Vec<RegionObligation<'tcx>>>,

    pub errors_will_be_reported: bool,
}

#[derive(Clone)]
pub struct RegionObligation<'tcx> {
    pub sub_region: ty::Region,
    pub sup_type: Ty<'tcx>,
    pub cause: ObligationCause<'tcx>,
}

impl<'tcx> FulfillmentContext<'tcx> {
    /// Creates a new fulfillment context.
    ///
    /// `errors_will_be_reported` indicates whether ALL errors that
    /// are generated by this fulfillment context will be reported to
    /// the end user. This is used to inform caching, because it
    /// allows us to conclude that traits that resolve successfully
    /// will in fact always resolve successfully (in particular, it
    /// guarantees that if some dependent obligation encounters a
    /// problem, compilation will be aborted).  If you're not sure of
    /// the right value here, pass `false`, as that is the more
    /// conservative option.
    ///
    /// FIXME -- a better option would be to hold back on modifying
    /// the global cache until we know that all dependent obligations
    /// are also satisfied. In that case, we could actually remove
    /// this boolean flag, and we'd also avoid the problem of squelching
    /// duplicate errors that occur across fns.
    pub fn new(errors_will_be_reported: bool) -> FulfillmentContext<'tcx> {
        FulfillmentContext {
            duplicate_set: FulfilledPredicates::new(),
            predicates: Vec::new(),
            attempted_mark: 0,
            region_obligations: NodeMap(),
            errors_will_be_reported: errors_will_be_reported,
        }
    }

    /// "Normalize" a projection type `<SomeType as SomeTrait>::X` by
    /// creating a fresh type variable `$0` as well as a projection
    /// predicate `<SomeType as SomeTrait>::X == $0`. When the
    /// inference engine runs, it will attempt to find an impl of
    /// `SomeTrait` or a where clause that lets us unify `$0` with
    /// something concrete. If this fails, we'll unify `$0` with
    /// `projection_ty` again.
    pub fn normalize_projection_type<'a>(&mut self,
                                         infcx: &InferCtxt<'a,'tcx>,
                                         projection_ty: ty::ProjectionTy<'tcx>,
                                         cause: ObligationCause<'tcx>)
                                         -> Ty<'tcx>
    {
        debug!("normalize_associated_type(projection_ty={:?})",
               projection_ty);

        assert!(!projection_ty.has_escaping_regions());

        // FIXME(#20304) -- cache

        let mut selcx = SelectionContext::new(infcx);
        let normalized = project::normalize_projection_type(&mut selcx, projection_ty, cause, 0);

        for obligation in normalized.obligations {
            self.register_predicate_obligation(infcx, obligation);
        }

        debug!("normalize_associated_type: result={:?}", normalized.value);

        normalized.value
    }

    pub fn register_builtin_bound<'a>(&mut self,
                                      infcx: &InferCtxt<'a,'tcx>,
                                      ty: Ty<'tcx>,
                                      builtin_bound: ty::BuiltinBound,
                                      cause: ObligationCause<'tcx>)
    {
        match predicate_for_builtin_bound(infcx.tcx, cause, builtin_bound, 0, ty) {
            Ok(predicate) => {
                self.register_predicate_obligation(infcx, predicate);
            }
            Err(ErrorReported) => { }
        }
    }

    pub fn register_region_obligation<'a>(&mut self,
                                          t_a: Ty<'tcx>,
                                          r_b: ty::Region,
                                          cause: ObligationCause<'tcx>)
    {
        register_region_obligation(t_a, r_b, cause, &mut self.region_obligations);
    }

    pub fn register_predicate_obligation<'a>(&mut self,
                                             infcx: &InferCtxt<'a,'tcx>,
                                             obligation: PredicateObligation<'tcx>)
    {
        // this helps to reduce duplicate errors, as well as making
        // debug output much nicer to read and so on.
        let obligation = infcx.resolve_type_vars_if_possible(&obligation);

        assert!(!obligation.has_escaping_regions());

        if self.is_duplicate_or_add(infcx.tcx, &obligation.predicate) {
            debug!("register_predicate({:?}) -- already seen, skip", obligation);
            return;
        }

        debug!("register_predicate({:?})", obligation);
        self.predicates.push(obligation);
    }

    pub fn region_obligations(&self,
                              body_id: ast::NodeId)
                              -> &[RegionObligation<'tcx>]
    {
        match self.region_obligations.get(&body_id) {
            None => Default::default(),
            Some(vec) => vec,
        }
    }

    pub fn select_all_or_error<'a>(&mut self,
                                   infcx: &InferCtxt<'a,'tcx>)
                                   -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        try!(self.select_where_possible(infcx));

        // Anything left is ambiguous.
        let errors: Vec<FulfillmentError> =
            self.predicates
            .iter()
            .map(|o| FulfillmentError::new((*o).clone(), CodeAmbiguity))
            .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    /// Attempts to select obligations that were registered since the call to a selection routine.
    /// This is used by the type checker to eagerly attempt to resolve obligations in hopes of
    /// gaining type information. It'd be equally valid to use `select_where_possible` but it
    /// results in `O(n^2)` performance (#18208).
    pub fn select_new_obligations<'a>(&mut self,
                                      infcx: &InferCtxt<'a,'tcx>)
                                      -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        let mut selcx = SelectionContext::new(infcx);
        self.select(&mut selcx, true)
    }

    pub fn select_where_possible<'a>(&mut self,
                                     infcx: &InferCtxt<'a,'tcx>)
                                     -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        let mut selcx = SelectionContext::new(infcx);
        self.select(&mut selcx, false)
    }

    pub fn pending_obligations(&self) -> &[PredicateObligation<'tcx>] {
        &self.predicates
    }

    fn is_duplicate_or_add(&mut self, tcx: &ty::ctxt<'tcx>,
                           predicate: &ty::Predicate<'tcx>)
                           -> bool {
        // This is a kind of dirty hack to allow us to avoid "rederiving"
        // things that we have already proven in other methods.
        //
        // The idea is that any predicate that doesn't involve type
        // parameters and which only involves the 'static region (and
        // no other regions) is universally solvable, since impls are global.
        //
        // This is particularly important since even if we have a
        // cache hit in the selection context, we still wind up
        // evaluating the 'nested obligations'.  This cache lets us
        // skip those.

        if self.errors_will_be_reported && predicate.is_global() {
            tcx.fulfilled_predicates.borrow_mut().is_duplicate_or_add(predicate)
        } else {
            self.duplicate_set.is_duplicate_or_add(predicate)
        }
    }

    /// Attempts to select obligations using `selcx`. If `only_new_obligations` is true, then it
    /// only attempts to select obligations that haven't been seen before.
    fn select<'a>(&mut self,
                  selcx: &mut SelectionContext<'a, 'tcx>,
                  only_new_obligations: bool)
                  -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        debug!("select({} obligations, only_new_obligations={}) start",
               self.predicates.len(),
               only_new_obligations);

        let mut errors = Vec::new();

        loop {
            let count = self.predicates.len();

            debug!("select_where_possible({} obligations) iteration",
                   count);

            let mut new_obligations = Vec::new();

            // If we are only attempting obligations we haven't seen yet,
            // then set `skip` to the number of obligations we've already
            // seen.
            let mut skip = if only_new_obligations {
                self.attempted_mark
            } else {
                0
            };

            // First pass: walk each obligation, retaining
            // only those that we cannot yet process.
            {
                let region_obligations = &mut self.region_obligations;
                self.predicates.retain(|predicate| {
                    // Hack: Retain does not pass in the index, but we want
                    // to avoid processing the first `start_count` entries.
                    let processed =
                        if skip == 0 {
                            process_predicate(selcx, predicate,
                                              &mut new_obligations, &mut errors, region_obligations)
                        } else {
                            skip -= 1;
                            false
                        };
                    !processed
                });
            }

            self.attempted_mark = self.predicates.len();

            if self.predicates.len() == count {
                // Nothing changed.
                break;
            }

            // Now go through all the successful ones,
            // registering any nested obligations for the future.
            for new_obligation in new_obligations {
                self.register_predicate_obligation(selcx.infcx(), new_obligation);
            }
        }

        debug!("select({} obligations, {} errors) done",
               self.predicates.len(),
               errors.len());

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

fn process_predicate<'a,'tcx>(selcx: &mut SelectionContext<'a,'tcx>,
                              obligation: &PredicateObligation<'tcx>,
                              new_obligations: &mut Vec<PredicateObligation<'tcx>>,
                              errors: &mut Vec<FulfillmentError<'tcx>>,
                              region_obligations: &mut NodeMap<Vec<RegionObligation<'tcx>>>)
                              -> bool
{
    /*!
     * Processes a predicate obligation and modifies the appropriate
     * output array with the successful/error result.  Returns `false`
     * if the predicate could not be processed due to insufficient
     * type inference.
     */

    match obligation.predicate {
        ty::Predicate::Trait(ref data) => {
            let trait_obligation = obligation.with(data.clone());
            match selcx.select(&trait_obligation) {
                Ok(None) => {
                    false
                }
                Ok(Some(s)) => {
                    new_obligations.append(&mut s.nested_obligations());
                    true
                }
                Err(selection_err) => {
                    debug!("predicate: {:?} error: {:?}",
                           obligation,
                           selection_err);
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeSelectionError(selection_err)));
                    true
                }
            }
        }

        ty::Predicate::Equate(ref binder) => {
            match selcx.infcx().equality_predicate(obligation.cause.span, binder) {
                Ok(()) => { }
                Err(_) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeSelectionError(Unimplemented)));
                }
            }
            true
        }

        ty::Predicate::RegionOutlives(ref binder) => {
            match selcx.infcx().region_outlives_predicate(obligation.cause.span, binder) {
                Ok(()) => { }
                Err(_) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeSelectionError(Unimplemented)));
                }
            }

            true
        }

        ty::Predicate::TypeOutlives(ref binder) => {
            // Check if there are higher-ranked regions.
            match selcx.tcx().no_late_bound_regions(binder) {
                // If there are, inspect the underlying type further.
                None => {
                    // Convert from `Binder<OutlivesPredicate<Ty, Region>>` to `Binder<Ty>`.
                    let binder = binder.map_bound_ref(|pred| pred.0);

                    // Check if the type has any bound regions.
                    match selcx.tcx().no_late_bound_regions(&binder) {
                        // If so, this obligation is an error (for now). Eventually we should be
                        // able to support additional cases here, like `for<'a> &'a str: 'a`.
                        None => {
                            errors.push(
                                FulfillmentError::new(
                                    obligation.clone(),
                                    CodeSelectionError(Unimplemented)))
                        }
                        // Otherwise, we have something of the form
                        // `for<'a> T: 'a where 'a not in T`, which we can treat as `T: 'static`.
                        Some(t_a) => {
                            register_region_obligation(t_a, ty::ReStatic,
                                                       obligation.cause.clone(),
                                                       region_obligations);
                        }
                    }
                }
                // If there aren't, register the obligation.
                Some(ty::OutlivesPredicate(t_a, r_b)) => {
                    register_region_obligation(t_a, r_b,
                                               obligation.cause.clone(),
                                               region_obligations);
                }
            }
            true
        }

        ty::Predicate::Projection(ref data) => {
            let project_obligation = obligation.with(data.clone());
            let result = project::poly_project_and_unify_type(selcx, &project_obligation);
            debug!("process_predicate: poly_project_and_unify_type({:?}) returned {:?}",
                   project_obligation,
                   result);
            match result {
                Ok(Some(obligations)) => {
                    new_obligations.extend(obligations);
                    true
                }
                Ok(None) => {
                    false
                }
                Err(err) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeProjectionError(err)));
                    true
                }
            }
        }

        ty::Predicate::WellFormed(ty) => {
            match wf::obligations(selcx.infcx(), obligation.cause.body_id,
                                  ty, obligation.cause.span) {
                Some(obligations) => {
                    new_obligations.extend(obligations);
                    true
                }
                None => {
                    false
                }
            }
        }
    }
}

impl<'tcx> fmt::Debug for RegionObligation<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "RegionObligation(sub_region={:?}, sup_type={:?})",
               self.sub_region,
               self.sup_type)
    }
}

fn register_region_obligation<'tcx>(t_a: Ty<'tcx>,
                                    r_b: ty::Region,
                                    cause: ObligationCause<'tcx>,
                                    region_obligations: &mut NodeMap<Vec<RegionObligation<'tcx>>>)
{
    let region_obligation = RegionObligation { sup_type: t_a,
                                               sub_region: r_b,
                                               cause: cause };

    debug!("register_region_obligation({:?}, cause={:?})",
           region_obligation, region_obligation.cause);

    region_obligations.entry(region_obligation.cause.body_id)
                      .or_insert(vec![])
                      .push(region_obligation);

}

impl<'tcx> FulfilledPredicates<'tcx> {
    pub fn new() -> FulfilledPredicates<'tcx> {
        FulfilledPredicates {
            set: HashSet::new()
        }
    }

    pub fn is_duplicate(&self, p: &ty::Predicate<'tcx>) -> bool {
        self.set.contains(p)
    }

    fn is_duplicate_or_add(&mut self, p: &ty::Predicate<'tcx>) -> bool {
        !self.set.insert(p.clone())
    }
}
