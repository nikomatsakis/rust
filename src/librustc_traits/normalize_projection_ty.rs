// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use rustc::infer::{InferCtxt, RegionObligation};
use rustc::infer::canonical::{Canonical, CanonicalVarValues, QueryResult, QueryRegionConstraints};
use rustc::infer::region_constraints::{Constraint, RegionConstraintData};
use rustc::traits::{self, FulfillmentContext, FulfillmentError, Normalized, ObligationCause,
                    SelectionContext};
use rustc::traits::query::{NoSolution, normalize::NormalizationResult};
use rustc::ty::{self, ParamEnvAnd, Ty, TyCtxt};
use std::rc::Rc;
use syntax::ast::{self, DUMMY_NODE_ID};
use syntax_pos::DUMMY_SP;

crate fn normalize_projection_ty<'tcx>(
    tcx: TyCtxt<'_, 'tcx, 'tcx>,
    goal: &'tcx Canonical<ParamEnvAnd<'tcx, ty::ProjectionTy<'tcx>>>,
) -> Result<Rc<Canonical<QueryResult<'tcx, NormalizationResult<'tcx>>>>, NoSolution> {
    debug!("normalize_provider(goal={:#?})", goal);

    tcx.infer_ctxt().enter(|ref infcx| {
        let tcx = infcx.tcx;
        let canonical_inference_vars =
            infcx.fresh_inference_vars_for_canonical_vars(DUMMY_SP, &goal.variables);
        let ParamEnvAnd {
            param_env,
            value: goal,
        } = goal.substitute(tcx, &canonical_inference_vars);
        let mut fulfill_cx = FulfillmentContext::new();
        let selcx = &mut SelectionContext::new(infcx);
        let cause = ObligationCause::misc(DUMMY_SP, DUMMY_NODE_ID);
        let Normalized {
            value: answer,
            obligations,
        } = traits::normalize_projection_type(selcx, param_env, goal, cause, 0);
        fulfill_cx.register_predicate_obligations(infcx, obligations);

        // Select everything, returning errors.
        let true_errors = match fulfill_cx.select_where_possible(infcx) {
            Ok(()) => vec![],
            Err(errors) => errors,
        };

        // Anything left unselected *now* must be an ambiguity.
        let ambig_errors = match fulfill_cx.select_all_or_error(infcx) {
            Ok(()) => vec![],
            Err(errors) => errors,
        };

        let region_obligations = infcx.take_registered_region_obligations();
        let region_constraints = infcx.take_and_reset_region_constraints();

        // Now that we have fulfilled as much as we can, create a solution
        // from what we've learned.
        make_normalize_solution(
            infcx,
            canonical_inference_vars,
            answer,
            region_obligations,
            region_constraints,
            true_errors,
            ambig_errors,
        )
    })
}

fn make_normalize_solution<'gcx, 'tcx>(
    infcx: &InferCtxt<'_, 'gcx, 'tcx>,
    inference_vars: CanonicalVarValues<'tcx>,
    answer: Ty<'tcx>,
    region_obligations: Vec<(ast::NodeId, RegionObligation<'tcx>)>,
    region_constraints: RegionConstraintData<'tcx>,
    true_errors: Vec<FulfillmentError<'tcx>>,
    ambig_errors: Vec<FulfillmentError<'tcx>>,
) -> Result<Rc<Canonical<QueryResult<'gcx, NormalizationResult<'gcx>>>>, NoSolution> {
    debug!(
        "make_normalize_solution(\
         inference_vars={:?}, \
         answer={:?}, \
         {} true_errors, \
         {} ambig_errors)",
        inference_vars,
        answer,
        true_errors.len(),
        ambig_errors.len(),
    );

    if !true_errors.is_empty() {
        // FIXME -- we don't indicate *why* we failed to solve
        debug!("make_normalize_solution: true_errors={:#?}", true_errors);
        return Err(NoSolution);
    }

    let RegionConstraintData {
        constraints,
        verifys,
        givens,
    } = region_constraints;

    let tcx = infcx.tcx;

    let region_outlives: Vec<_> = constraints
        .into_iter()
        .map(|(k, _)| match k {
            Constraint::VarSubVar(v1, v2) => {
                (tcx.mk_region(ty::ReVar(v1)), tcx.mk_region(ty::ReVar(v2)))
            }
            Constraint::VarSubReg(v1, r2) => (tcx.mk_region(ty::ReVar(v1)), r2),
            Constraint::RegSubVar(r1, v2) => (r1, tcx.mk_region(ty::ReVar(v2))),
            Constraint::RegSubReg(r1, r2) => (r1, r2),
        })
        .collect();

    let ty_outlives: Vec<_> = region_obligations
        .into_iter()
        .map(|(_, r_o)| (r_o.sup_type, r_o.sub_region))
        .collect();

    assert!(verifys.is_empty());
    assert!(givens.is_empty());

    let (canonical_result, _) = infcx.canonicalize_response(&QueryResult {
        var_values: inference_vars,
        region_constraints: QueryRegionConstraints {
            region_outlives,
            ty_outlives,
        },
        value: NormalizationResult {
            normalized_ty: answer,
            ambiguity: !ambig_errors.is_empty(),
        },
    });

    debug!(
        "make_normalize_solution: canonical_result = {:#?}",
        canonical_result
    );

    Ok(canonical_result)
}
