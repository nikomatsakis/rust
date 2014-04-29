// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::subst::VecPerParamSpace;
use middle::ty;
use middle::typeck::infer::InferCtxt;
use std::rc::Rc;
use util::common::unstable_partition;
use util::promise::Promise;
use util::ppaux::Repr;

use super::Ambiguity;
use super::Obligation;
use super::FulfillmentError;
use super::FulfillmentErrorCode;
use super::Selection;
use super::SelectionError;
use super::SelectionResult;
use super::select::SelectionContext;
use super::Vtable;

/**
 * The fulfillment context is used to drive trait resolution.  It
 * consists of a list of obligations that must be (eventually)
 * satisfied.  The owner can add new obligations to this list and get
 * back a promise (`PendingSelection`) in return. The `select_*`
 * methods are used to try and find origins for each of the the
 * registered selections -- whenever a registered obligation has been
 * satisfied, or we determine that it can never be satisfied, the
 * associated promise will be fulfilled, either with a selection or
 * with an error, as appropriate.
 */
pub struct FulfillmentContext {
    // A list of all obligations that have been registered with this
    // fulfillment context. The list is kept partitioned, with the
    // selected obligations coming first and the unselected coming
    // second. (See `selected_obligations_count`.)
    registered_obligations: Vec<RegisteredObligation>,

    // Number of entries in `registered` that have been selected.
    selected_obligations_count: uint,
}

/**
 * An obligation that has been registered with a `FulfillmentContext`.
 * The fulfillment context internally stores both the obligation and
 * the promise that must be fulfilled once the obligation has been
 * selected.
 */
struct RegisteredObligation {
    obligation: Obligation,
    selection: PendingSelection,
}

/**
 * The promise associated with each registered obligation. When/if the
 * origin for the obligation has been selected, this promise will be
 * fulfilled. Note that it may be fulfilled with an error.
 */
#[deriving(Show,Clone)]
pub struct PendingSelection {
    pub promise: Rc<Promise<Result<PendingVtableOrigin, SelectionError>>>
}
pub type PendingSelections = VecPerParamSpace<PendingSelection>;

/**
 * A vtable whose nested obligations are promises.
 */
pub type PendingVtableOrigin = Vtable<PendingSelection>;
pub type PendingVtableOrigins = VecPerParamSpace<PendingVtableOrigin>;

impl FulfillmentContext {
    pub fn new() -> FulfillmentContext {
        FulfillmentContext { registered_obligations: Vec::new(),
                             selected_obligations_count: 0 }
    }

    pub fn register_obligation(&mut self,
                               tcx: &ty::ctxt,
                               obligation: Obligation)
                               -> PendingSelection
    {
        debug!("add_obligation({})", obligation.repr(tcx));
        let pending_selection =
            PendingSelection { promise: Rc::new(Promise::new()) };
        let registered_obligation =
            RegisteredObligation { obligation: obligation,
                                   selection: pending_selection.clone() };
        self.registered_obligations.push(registered_obligation);
        pending_selection
    }

    pub fn select_all_or_error<'a>(&'a mut self,
                                   infcx: &InferCtxt,
                                   param_env: &ty::ParameterEnvironment)
                                   -> Result<(),FulfillmentError<'a>>
    {
        self.select_where_possible(infcx, param_env);

        // Check for obligations that were selected with an error or
        // which could not be selected at all.
        for f_o in self.registered_obligations.iter() {
            match f_o.selection.promise.get() {
                Some(&Ok(_)) => continue,
                Some(&Err(ref e)) => {
                    let e = (*e).clone();
                    return Err(FulfillmentError::new(&f_o.obligation,
                                                     SelectionError(e)));
                }
                None => {
                    return Err(FulfillmentError::new(&f_o.obligation,
                                                     Ambiguity));
                }
            }
        }

        Ok(())
    }

    pub fn select_where_possible(&mut self,
                                 infcx: &InferCtxt,
                                 param_env: &ty::ParameterEnvironment)
                                 -> bool
    {
        /*!
         * Iterate over any pending obligations that have not yet been
         * resolved and try to resolve them. Each time a pending
         * obligation is resolved, it is moved to the front of the
         * list. Furthermore, any nested obligations are converted into
         * new pending selections and added to the end of the list. This
         * process repeats so long as progress is being made (so there is
         * no point in calling twice in a row). Returns true if anything
         * was successfully resolved, or false otherwise. A true result
         * indicates that more type information *may* be available.
         */

        let tcx = infcx.tcx;
        let selcx = SelectionContext::new(infcx, param_env);
        let original_selected = self.selected_obligations_count;

        debug!("select_where_possible({}/{} selected) start",
               original_selected,
               self.registered_obligations.len());

        // Invariant: indices in range {0 <= _ < selected} are selected.
        let mut selected = original_selected;

        loop {
            // We have to be somewhat careful here because the list of
            // obligations cannot be borrowed while we append to it.
            // Therefore this process proceeds in various stages.

            // First try to resolve all of the pending obligations.
            let selections =
                self.try_select_pending_obligations(&selcx, selected);

            // Next register any new obligations to convert them into
            // pending obligations. This step modifies
            // `fcx.inh.pending_obligations` so we must be careful to
            // ensure it is not borrowed at this time.
            let selections =
                self.register_new_selections(tcx, selections);

            // Fulfill any promises that need to be selected.
            let pending_obligations =
                self.registered_obligations.mut_slice(
                    selected,
                    selected + selections.len());
            fulfill_promises(tcx, pending_obligations, selections);

            // Finally partition any items whose promises are fulfilled to
            // the front of the list.
            let newly_selected =
                unstable_partition(pending_obligations,
                                   |p_o| !p_o.selection.promise.is_fulfilled());

            // increment total number of selected obligations. break
            // if no progress.
            if newly_selected == 0 {
                break;
            }
            selected += newly_selected;
        }

        debug!("try_resolve_fcx_obligations({}/{} selected) end",
               selected,
               self.registered_obligations.len());

        self.selected_obligations_count = selected;
        return selected != original_selected;
    }

    fn try_select_pending_obligations(&mut self,
                                      selcx: &SelectionContext,
                                      selected: uint)
                                      -> Vec<SelectionResult<Selection>>
    {
        /*!
         * For those obligations that are still pending, run the
         * selection process.
         */

        let pending_obligations =
            self.registered_obligations.slice_from(selected);
        pending_obligations
            .iter()
            .map(|o| selcx.select(&o.obligation))
            .collect()
    }

    fn register_new_selections(&mut self,
                               tcx: &ty::ctxt,
                               selections: Vec<SelectionResult<Selection>>)
                               -> Vec<SelectionResult<PendingVtableOrigin>>
    {
        /*!
         * Go through each new selection from this round. For those
         * that were successful, take each of the nested obligations
         * and register it, replacing it with the `PendingSelection`.
         * Note that this may modify the `self.registered_obligations`
         * vector.
         */

        selections.move_iter().map(|r| {
            match r {
                Err(e) => Err(e),
                Ok(None) => Ok(None),
                Ok(Some(v)) => {
                    Ok(Some(v.map_move_nested(
                        |o| self.register_obligation(tcx, o))))
                }
            }
        }).collect()
    }
}

fn fulfill_promises(tcx: &ty::ctxt,
                    pending_obligations: &[RegisteredObligation],
                    selections: Vec<SelectionResult<PendingVtableOrigin>>)
{
    /*!
     * For each of the entries in `pending_obligations`, check
     * whether there is a corresponding selection (either
     * successful, or error) in `selections`. If so, fulfill the
     * promise.
     */

    for (p_o, r) in pending_obligations.iter().zip(selections.move_iter()) {
        match r {
            Err(e) => {
                debug!("obligation {} failed to resolve: {}",
                       p_o.obligation.repr(tcx),
                       e);
                p_o.selection.promise.fulfill(Err(e)).unwrap();
            }
            Ok(Some(r)) => {
                debug!("obligation {} selected to: {}",
                       p_o.obligation.repr(tcx),
                       r.repr(tcx));
                p_o.selection.promise.fulfill(Ok(r)).unwrap();
            }
            Ok(None) => {
                debug!("obligation not yet selected");
            }
        }
    }
}

impl Repr for RegisteredObligation {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        format!("RegisteredObligation({},{})",
                self.obligation.repr(tcx),
                self.selection.repr(tcx))
    }
}

impl Repr for PendingSelection {
    fn repr(&self, tcx: &ty::ctxt) -> String {
        self.promise.repr(tcx)
    }
}

