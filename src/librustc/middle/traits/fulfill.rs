// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::infer::{mod, InferCtxt};
use middle::mem_categorization::Typer;
use middle::ty::{mod, AsPredicate, RegionEscape, Ty, ToPolyTraitRef};
use std::collections::HashSet;
use std::collections::hash_map::Entry::{Occupied, Vacant};
use std::default::Default;
use std::rc::Rc;
use syntax::ast;
use util::common::ErrorReported;
use util::ppaux::Repr;
use util::nodemap::NodeMap;

use super::CodeAmbiguity;
use super::CodeProjectionError;
use super::CodeSelectionError;
use super::FulfillmentError;
use super::Obligation;
use super::ObligationCause;
use super::PredicateObligation;
use super::project;
use super::select::SelectionContext;
use super::Unimplemented;
use super::util::predicate_for_builtin_bound;

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
    duplicate_set: HashSet<ty::Predicate<'tcx>>,

    // A list of all obligations that have been registered with this
    // fulfillment context.
    predicates: Vec<PredicateObligation<'tcx>>,

    // Remembers the count of trait obligations that we have already
    // attempted to select. This is used to avoid repeating work
    // when `select_new_obligations` is called.
    attempted_mark: uint,

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
}

pub struct RegionObligation<'tcx> {
    pub sub_region: ty::Region,
    pub sup_type: Ty<'tcx>,
    pub cause: ObligationCause<'tcx>,
}

impl<'tcx> FulfillmentContext<'tcx> {
    pub fn new() -> FulfillmentContext<'tcx> {
        FulfillmentContext {
            duplicate_set: HashSet::new(),
            predicates: Vec::new(),
            attempted_mark: 0,
            region_obligations: NodeMap::new(),
        }
    }

    pub fn normalize_associated_type<'a>(&mut self,
                                         infcx: &InferCtxt<'a,'tcx>,
                                         trait_ref: Rc<ty::TraitRef<'tcx>>,
                                         item_name: ast::Name,
                                         cause: ObligationCause<'tcx>)
                                         -> Ty<'tcx>
    {
        assert!(!trait_ref.has_escaping_regions());

        let ty_var = infcx.next_ty_var();
        let projection =
            ty::Binder(ty::ProjectionPredicate {
                projection_ty: ty::ProjectionTy { trait_ref: trait_ref,
                                                  item_name: item_name },
                ty: ty_var
            });
        let obligation = Obligation::new(cause, projection.as_predicate());
        self.register_predicate(infcx.tcx, obligation);
        ty_var
    }

    pub fn register_builtin_bound(&mut self,
                                  tcx: &ty::ctxt<'tcx>,
                                  ty: Ty<'tcx>,
                                  builtin_bound: ty::BuiltinBound,
                                  cause: ObligationCause<'tcx>)
    {
        match predicate_for_builtin_bound(tcx, cause, builtin_bound, 0, ty) {
            Ok(predicate) => {
                self.register_predicate(tcx, predicate);
            }
            Err(ErrorReported) => { }
        }
    }

    pub fn register_region_obligation(&mut self,
                                      tcx: &ty::ctxt<'tcx>,
                                      t_a: Ty<'tcx>,
                                      r_b: ty::Region,
                                      cause: ObligationCause<'tcx>)
    {
        register_region_obligation(tcx, t_a, r_b, cause, &mut self.region_obligations);
    }

    pub fn register_predicate<'a>(&mut self,
                                  tcx: &ty::ctxt<'tcx>,
                                  obligation: PredicateObligation<'tcx>)
    {
        if !self.duplicate_set.insert(obligation.predicate.clone()) {
            debug!("register_predicate({}) -- already seen, skip", obligation.repr(tcx));
            return;
        }

        debug!("register_predicate({})", obligation.repr(tcx));
        self.predicates.push(obligation);
    }

    pub fn region_obligations(&self,
                              body_id: ast::NodeId)
                              -> &[RegionObligation<'tcx>]
    {
        match self.region_obligations.get(&body_id) {
            None => Default::default(),
            Some(vec) => vec.as_slice(),
        }
    }

    pub fn select_all_or_error<'a>(&mut self,
                                   infcx: &InferCtxt<'a,'tcx>,
                                   param_env: &ty::ParameterEnvironment<'tcx>,
                                   typer: &Typer<'tcx>)
                                   -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        try!(self.select_where_possible(infcx, param_env, typer));

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
                                      infcx: &InferCtxt<'a,'tcx>,
                                      param_env: &ty::ParameterEnvironment<'tcx>,
                                      typer: &Typer<'tcx>)
                                      -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        let mut selcx = SelectionContext::new(infcx, param_env, typer);
        self.select(&mut selcx, true)
    }

    pub fn select_where_possible<'a>(&mut self,
                                     infcx: &InferCtxt<'a,'tcx>,
                                     param_env: &ty::ParameterEnvironment<'tcx>,
                                     typer: &Typer<'tcx>)
                                     -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        let mut selcx = SelectionContext::new(infcx, param_env, typer);
        self.select(&mut selcx, false)
    }

    pub fn pending_obligations(&self) -> &[PredicateObligation<'tcx>] {
        self.predicates[]
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

        let tcx = selcx.tcx();
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
            for new_obligation in new_obligations.into_iter() {
                self.register_predicate(tcx, new_obligation);
            }
        }

        debug!("select({} obligations, {} errors) done",
               self.predicates.len(),
               errors.len());

        if errors.len() == 0 {
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

    let tcx = selcx.tcx();
    match obligation.predicate {
        ty::Predicate::Trait(ref data) => {
            let trait_obligation = obligation.with(data.clone());
            match selcx.select(&trait_obligation) {
                Ok(None) => {
                    false
                }
                Ok(Some(s)) => {
                    s.map_move_nested(|p| new_obligations.push(p));
                    true
                }
                Err(selection_err) => {
                    debug!("predicate: {} error: {}",
                           obligation.repr(tcx),
                           selection_err.repr(tcx));
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
            // For now, we just check that there are no higher-ranked
            // regions.  If there are, we will call this obligation an
            // error. Eventually we should be able to support some
            // cases here, I imagine (e.g., `for<'a> int : 'a`).
            if ty::count_late_bound_regions(selcx.tcx(), binder) != 0 {
                errors.push(
                    FulfillmentError::new(
                        obligation.clone(),
                        CodeSelectionError(Unimplemented)));
            } else {
                let ty::OutlivesPredicate(t_a, r_b) = binder.0;
                register_region_obligation(tcx, t_a, r_b,
                                           obligation.cause.clone(),
                                           region_obligations);
            }
            true
        }

        ty::Predicate::Projection(ref data) => {
            let project_obligation = obligation.with(data.clone());
            let result = project::poly_project_and_unify_type(selcx, &project_obligation);
            debug!("poly_project_and_unify_type({}) = {}",
                   project_obligation.repr(tcx),
                   result.repr(tcx));
            match result {
                Ok(()) => {
                    true
                }
                Err(project::ProjectionError::TooManyCandidates) => {
                    // Without more type information, we can't say much.
                    false
                }
                Err(project::ProjectionError::NoCandidate) => {
                    // This means that we have a type like `<T as
                    // Trait>::name = U` but we couldn't find any more
                    // information. This could just be that we're in a
                    // function like:
                    //
                    //     fn foo<T:Trait>(...)
                    //
                    // in which case this is not an error. But it
                    // might also mean we're in a situation where we
                    // don't actually know that `T : Trait` holds,
                    // which would be weird (e.g., if `T` was not a
                    // parameter type but a normal type, like `int`).
                    //
                    // So what we do is to (1) add a requirement that
                    // `T : Trait` (just in case) and (2) try to unify
                    // `U` with `<T as Trait>::name`.

                    if !ty::binds_late_bound_regions(selcx.tcx(), data) {
                        // Check that `T : Trait` holds.
                        let trait_ref = data.to_poly_trait_ref();
                        new_obligations.push(obligation.with(trait_ref.as_predicate()));

                        // Fallback to `<T as Trait>::name`. If this
                        // fails, then the output must be at least
                        // somewhat constrained, and we cannot verify
                        // that constraint, so yield an error.
                        let ty_projection = ty::mk_projection(tcx,
                                                             (*trait_ref.0).clone(),
                                                             data.0.projection_ty.item_name);

                        debug!("process_predicate: falling back to projection {}",
                               ty_projection.repr(selcx.tcx()));

                        match infer::mk_eqty(selcx.infcx(),
                                             true,
                                             infer::EquatePredicate(obligation.cause.span),
                                             ty_projection,
                                             data.0.ty) {
                            Ok(()) => { }
                            Err(_) => {
                                debug!("process_predicate: fallback failed to unify; error");
                                errors.push(
                                    FulfillmentError::new(
                                        obligation.clone(),
                                        CodeSelectionError(Unimplemented)));
                            }
                        }

                        true
                    } else {
                        // If we have something like
                        //
                        //     for<'a> <T<'a> as Trait>::name == &'a int
                        //
                        // there is no "canonical form" for us to
                        // make, so just report the lack of candidates
                        // as an error.

                        debug!("process_predicate: can't fallback, higher-ranked");
                        errors.push(
                            FulfillmentError::new(
                                obligation.clone(),
                                CodeSelectionError(Unimplemented)));

                        true
                    }
                }
                Err(project::ProjectionError::MismatchedTypes(e)) => {
                    errors.push(
                        FulfillmentError::new(
                            obligation.clone(),
                            CodeProjectionError(e)));
                    true
                }
                Err(project::ProjectionError::TraitSelectionError(e)) => {
                    // Extract just the `T : Trait` from `<T as
                    // Trait>::Name == U`, so that when we report an
                    // error to the user, it says something like "`T :
                    // Trait` not satisfied".5D
                    let trait_predicate = data.to_poly_trait_ref();
                    let trait_obligation = obligation.with(trait_predicate.as_predicate());
                    errors.push(
                        FulfillmentError::new(
                            trait_obligation,
                            CodeSelectionError(e)));
                    true
                }
            }
        }
    }
}

impl<'tcx> Repr<'tcx> for RegionObligation<'tcx> {
    fn repr(&self, tcx: &ty::ctxt<'tcx>) -> String {
        format!("RegionObligation(sub_region={}, sup_type={})",
                self.sub_region.repr(tcx),
                self.sup_type.repr(tcx))
    }
}

fn register_region_obligation<'tcx>(tcx: &ty::ctxt<'tcx>,
                                    t_a: Ty<'tcx>,
                                    r_b: ty::Region,
                                    cause: ObligationCause<'tcx>,
                                    region_obligations: &mut NodeMap<Vec<RegionObligation<'tcx>>>)
{
    let region_obligation = RegionObligation { sup_type: t_a,
                                               sub_region: r_b,
                                               cause: cause };

    debug!("register_region_obligation({})",
           region_obligation.repr(tcx));

    match region_obligations.entry(region_obligation.cause.body_id) {
        Vacant(entry) => { entry.set(vec![region_obligation]); },
        Occupied(mut entry) => { entry.get_mut().push(region_obligation); },
    }

}

