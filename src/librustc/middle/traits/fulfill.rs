// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::mem_categorization::Typer;
use middle::ty;
use middle::typeck::infer;
use middle::typeck::infer::InferCtxt;
use std::collections::hashmap::{Vacant,Occupied};
use util::nodemap::NodeMap;
use util::ppaux::Repr;

use super::CodeAmbiguity;
use super::CodeSelectionError;
use super::FulfillmentError;
use super::Obligation;
use super::PredicateObligation;
use super::select::SelectionContext;
use super::TraitObligation;

/**
 * The fulfillment context is used to drive trait resolution.  It
 * consists of a list of obligations that must be (eventually)
 * satisfied. The job is to track which are satisfied, which yielded
 * errors, and which are still pending. At any point, users can call
 * `select_where_possible`, and the fulfilment context will try to do
 * selection, retaining only those obligations that remain
 * ambiguous. This may be helpful in pushing type inference
 * along. Once all type inference constraints have been generated, the
 * method `select_all_or_error` can be used to report any remaining
 * ambiguous cases as errors.
 */
pub struct FulfillmentContext {
    // A list of all obligations that have been registered with this
    // fulfillment context.
    trait_obligations: Vec<TraitObligation>,

    // As we process traits, we also accumulate constraints on the
    // lifetime bounding various types. Each constraint has the form
    // `T:'a`, meaning "some type `T` must outlive the lifetime
    // 'a". These constraints derive from instantiated type
    // parameters. So if you had a struct defined like
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
    // place. The reason that we store under thef n-id, and not
    // something more fine-grained, is so that it is easier for
    // regionck to be sure that it has found *all* the region
    // obligations (otherwise, it's easy to fail to walk to a
    // particular node-id).
    region_obligations: NodeMap<Vec<RegionObligation>>,
    // Remembers the count of trait obligations that we have already
    // attempted to select. This is used to avoid repeating work
    // when `select_new_obligations` is called.
    attempted_mark: uint,
}

pub struct RegionObligation {
    sub_region: ty::Region,
    sup_type: ty::t,
    origin: infer::SubregionOrigin,
}

impl FulfillmentContext {
    pub fn new() -> FulfillmentContext {
        FulfillmentContext {
            trait_obligations: Vec::new(),
            region_obligations: NodeMap::new(),
            attempted_mark: 0
        }
    }

    pub fn register_trait_ref_obligation(&mut self,
                                         infcx: &InferCtxt,
                                         obligation: TraitObligation)
    {
        let obligation =
            obligation.with_predicate(
                ty::TraitPredicate(obligation.predicate.clone()));
        self.register_obligation(infcx, obligation)
    }

    pub fn register_obligation(&mut self,
                               infcx: &InferCtxt,
                               obligation: PredicateObligation)
    {
        let tcx = infcx.tcx;
        debug!("register_obligation({})", obligation.repr(tcx));
        let Obligation { cause, recursion_depth, predicate } = obligation;
        match predicate {
            ty::TraitPredicate(trait_ref) => {
                self.trait_obligations.push(Obligation { cause: cause,
                                                         recursion_depth: recursion_depth,
                                                         predicate: trait_ref });
            }

            ty::OutlivesPredicate(ty::TypeOutlivesPredicate(t, r)) => {
                // Constraints like `T:'a` we must record for later.
                // Currently, regionck handles these, though I'd
                // prefer to push this reasoning into the inference
                // context itself eventually.
                let origin = infer::RelateParamBound(cause.span, t);
                let region_obligation = RegionObligation { origin: origin,
                                                           sup_type: t,
                                                           sub_region: r, };
                match self.region_obligations.entry(cause.body_id) {
                    Vacant(entry) => { entry.set(vec![region_obligation]); },
                    Occupied(mut entry) => { entry.get_mut().push(region_obligation); },
                }
            }

            ty::OutlivesPredicate(ty::RegionOutlivesPredicate(sup_region, sub_region)) => {
                // Subregions we can refer directly to the infcx.
                let origin = infer::RelateRegionParamBound(cause.span);
                infcx.sub_regions(origin, sub_region, sup_region);
            }
        }
    }

    pub fn select_all_or_error<'a,'tcx>(&mut self,
                                        infcx: &InferCtxt<'a,'tcx>,
                                        param_env: &ty::ParameterEnvironment,
                                        typer: &Typer<'tcx>)
                                        -> Result<(),Vec<FulfillmentError>>
    {
        try!(self.select_where_possible(infcx, param_env, typer));

        // Anything left is ambiguous.
        let errors: Vec<FulfillmentError> =
            self.trait_obligations
            .iter()
            .map(|o| FulfillmentError::new((*o).clone(), CodeAmbiguity))
            .collect();

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub fn select_new_obligations<'a,'tcx>(&mut self,
                                           infcx: &InferCtxt<'a,'tcx>,
                                           param_env: &ty::ParameterEnvironment,
                                           typer: &Typer<'tcx>)
                                           -> Result<(),Vec<FulfillmentError>>
    {
        /*!
         * Attempts to select obligations that were registered since
         * the call to a selection routine. This is used by the type checker
         * to eagerly attempt to resolve obligations in hopes of gaining
         * type information. It'd be equally valid to use `select_where_possible`
         * but it results in `O(n^2)` performance (#18208).
         */

        let mut selcx = SelectionContext::new(infcx, param_env, typer);
        self.select(&mut selcx, true)
    }

    pub fn select_where_possible<'a,'tcx>(&mut self,
                                          infcx: &InferCtxt<'a,'tcx>,
                                          param_env: &ty::ParameterEnvironment,
                                          typer: &Typer<'tcx>)
                                          -> Result<(),Vec<FulfillmentError>>
    {
        let mut selcx = SelectionContext::new(infcx, param_env, typer);
        self.select(&mut selcx, false)
    }

    fn select(&mut self,
              selcx: &mut SelectionContext,
              only_new_obligations: bool)
              -> Result<(),Vec<FulfillmentError>>
    {
        /*!
         * Attempts to select obligations using `selcx`. If
         * `only_new_obligations` is true, then it only attempts to
         * select obligations that haven't been seen before.
         */
        debug!("select({} obligations, only_new_obligations={}) start",
               self.trait_obligations.len(),
               only_new_obligations);

        let tcx = selcx.tcx();
        let infcx = selcx.infcx();
        let mut errors = Vec::new();

        loop {
            let count = self.trait_obligations.len();

            debug!("select_where_possible({} obligations) iteration",
                   count);

            let mut selections = Vec::new();

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
            self.trait_obligations.retain(|obligation| {
                // Hack: Retain does not pass in the index, but we want
                // to avoid processing the first `start_count` entries.
                if skip > 0 {
                    skip -= 1;
                    true
                } else {
                    match selcx.select(obligation) {
                        Ok(None) => {
                            true
                        }
                        Ok(Some(s)) => {
                            selections.push(s);
                            false
                        }
                        Err(selection_err) => {
                            debug!("obligation: {} error: {}",
                                   obligation.repr(tcx),
                                   selection_err.repr(tcx));
                            errors.push(FulfillmentError::new(
                                (*obligation).clone(),
                                CodeSelectionError(selection_err)));
                            false
                        }
                    }
                }
            });

            self.attempted_mark = self.trait_obligations.len();

            if self.trait_obligations.len() == count {
                // Nothing changed.
                break;
            }

            // Now go through all the successful ones,
            // registering any nested obligations for the future.
            for selection in selections.into_iter() {
                selection.map_move_nested(
                    |o| self.register_obligation(infcx, o));
            }
        }

        debug!("select({} obligations, {} errors) done",
               self.trait_obligations.len(),
               errors.len());

        if errors.len() == 0 {
            Ok(())
        } else {
            Err(errors)
        }
    }
}
