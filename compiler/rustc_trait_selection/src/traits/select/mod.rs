//! Candidate selection. See the [rustc dev guide] for more information on how this works.
//!
//! [rustc dev guide]: https://rustc-dev-guide.rust-lang.org/traits/resolution.html#selection

use self::stack::ProvisionalEvaluationCache;
use self::stack::{TraitObligationStack, TraitObligationStackList};
use self::EvaluationResult::*;
use self::SelectionCandidate::*;

use super::coherence::{self, Conflict};
use super::const_evaluatable;
use super::project;
use super::project::normalize_with_depth_to;
use super::project::ProjectionTyObligation;
use super::util;
use super::util::{closure_trait_ref_and_return_type, predicate_for_trait_def};
use super::wf;
use super::DerivedObligationCause;
use super::Obligation;
use super::ObligationCauseCode;
use super::Selection;
use super::SelectionResult;
use super::TraitQueryMode;
use super::{Normalized, ProjectionCacheKey};
use super::{ObligationCause, PredicateObligation, TraitObligation};
use super::{Overflow, SelectionError, Unimplemented};

use crate::infer::{InferCtxt, InferOk, TypeFreshener};
use crate::traits::error_reporting::InferCtxtExt;
use crate::traits::project::ProjectionCacheKeyExt;
use rustc_data_structures::fx::FxHashSet;
use rustc_data_structures::stack::ensure_sufficient_stack;
use rustc_errors::ErrorReported;
use rustc_hir as hir;
use rustc_hir::def_id::DefId;
use rustc_hir::Constness;
use rustc_infer::infer::LateBoundRegionConversionTime;
use rustc_middle::dep_graph::{DepKind, DepNodeIndex};
use rustc_middle::mir::abstract_const::NotConstEvaluatable;
use rustc_middle::mir::interpret::ErrorHandled;
use rustc_middle::ty::fast_reject;
use rustc_middle::ty::print::with_no_trimmed_paths;
use rustc_middle::ty::relate::TypeRelation;
use rustc_middle::ty::subst::{GenericArgKind, Subst, SubstsRef};
use rustc_middle::ty::{self, PolyProjectionPredicate, ToPolyTraitRef, ToPredicate};
use rustc_middle::ty::{Ty, TyCtxt, TypeFoldable, WithConstness};
use rustc_span::symbol::sym;

use std::cell::Cell;
use std::cmp;
use std::fmt::Display;
use std::iter;
use std::rc::Rc;

pub use rustc_middle::traits::select::*;

mod candidate_assembly;
mod confirmation;
mod stack;

#[derive(Clone, Debug)]
pub enum IntercrateAmbiguityCause {
    DownstreamCrate { trait_desc: String, self_desc: Option<String> },
    UpstreamCrateUpdate { trait_desc: String, self_desc: Option<String> },
    ReservationImpl { message: String },
}

impl IntercrateAmbiguityCause {
    /// Emits notes when the overlap is caused by complex intercrate ambiguities.
    /// See #23980 for details.
    pub fn add_intercrate_ambiguity_hint(&self, err: &mut rustc_errors::DiagnosticBuilder<'_>) {
        err.note(&self.intercrate_ambiguity_hint());
    }

    pub fn intercrate_ambiguity_hint(&self) -> String {
        match self {
            IntercrateAmbiguityCause::DownstreamCrate { trait_desc, self_desc } => {
                let self_desc = if let Some(ty) = self_desc {
                    format!(" for type `{}`", ty)
                } else {
                    String::new()
                };
                format!("downstream crates may implement trait `{}`{}", trait_desc, self_desc)
            }
            IntercrateAmbiguityCause::UpstreamCrateUpdate { trait_desc, self_desc } => {
                let self_desc = if let Some(ty) = self_desc {
                    format!(" for type `{}`", ty)
                } else {
                    String::new()
                };
                format!(
                    "upstream crates may add a new impl of trait `{}`{} \
                     in future versions",
                    trait_desc, self_desc
                )
            }
            IntercrateAmbiguityCause::ReservationImpl { message } => message.clone(),
        }
    }
}

pub struct SelectionContext<'cx, 'tcx> {
    infcx: &'cx InferCtxt<'cx, 'tcx>,

    /// Freshener used specifically for entries on the obligation
    /// stack. This ensures that all entries on the stack at one time
    /// will have the same set of placeholder entries, which is
    /// important for checking for trait bounds that recursively
    /// require themselves.
    freshener: TypeFreshener<'cx, 'tcx>,

    /// If `true`, indicates that the evaluation should be conservative
    /// and consider the possibility of types outside this crate.
    /// This comes up primarily when resolving ambiguity. Imagine
    /// there is some trait reference `$0: Bar` where `$0` is an
    /// inference variable. If `intercrate` is true, then we can never
    /// say for sure that this reference is not implemented, even if
    /// there are *no impls at all for `Bar`*, because `$0` could be
    /// bound to some type that in a downstream crate that implements
    /// `Bar`. This is the suitable mode for coherence. Elsewhere,
    /// though, we set this to false, because we are only interested
    /// in types that the user could actually have written --- in
    /// other words, we consider `$0: Bar` to be unimplemented if
    /// there is no type that the user could *actually name* that
    /// would satisfy it. This avoids crippling inference, basically.
    intercrate: bool,

    intercrate_ambiguity_causes: Option<Vec<IntercrateAmbiguityCause>>,

    /// Controls whether or not to filter out negative impls when selecting.
    /// This is used in librustdoc to distinguish between the lack of an impl
    /// and a negative impl
    allow_negative_impls: bool,

    /// The mode that trait queries run in, which informs our error handling
    /// policy. In essence, canonicalized queries need their errors propagated
    /// rather than immediately reported because we do not have accurate spans.
    query_mode: TraitQueryMode,
}

struct SelectionCandidateSet<'tcx> {
    // A list of candidates that definitely apply to the current
    // obligation (meaning: types unify).
    vec: Vec<SelectionCandidate<'tcx>>,

    // If `true`, then there were candidates that might or might
    // not have applied, but we couldn't tell. This occurs when some
    // of the input types are type variables, in which case there are
    // various "builtin" rules that might or might not trigger.
    ambiguous: bool,
}

#[derive(PartialEq, Eq, Debug, Clone)]
struct EvaluatedCandidate<'tcx> {
    candidate: SelectionCandidate<'tcx>,
    evaluation: EvaluationResult,
}

/// When does the builtin impl for `T: Trait` apply?
enum BuiltinImplConditions<'tcx> {
    /// The impl is conditional on `T1, T2, ...: Trait`.
    Where(ty::Binder<'tcx, Vec<Ty<'tcx>>>),
    /// There is no built-in impl. There may be some other
    /// candidate (a where-clause or user-defined impl).
    None,
    /// It is unknown whether there is an impl.
    Ambiguous,
}

impl<'cx, 'tcx> SelectionContext<'cx, 'tcx> {
    pub fn new(infcx: &'cx InferCtxt<'cx, 'tcx>) -> SelectionContext<'cx, 'tcx> {
        SelectionContext {
            infcx,
            freshener: infcx.freshener(),
            intercrate: false,
            intercrate_ambiguity_causes: None,
            allow_negative_impls: false,
            query_mode: TraitQueryMode::Standard,
        }
    }

    pub fn intercrate(infcx: &'cx InferCtxt<'cx, 'tcx>) -> SelectionContext<'cx, 'tcx> {
        SelectionContext {
            infcx,
            freshener: infcx.freshener(),
            intercrate: true,
            intercrate_ambiguity_causes: None,
            allow_negative_impls: false,
            query_mode: TraitQueryMode::Standard,
        }
    }

    pub fn with_negative(
        infcx: &'cx InferCtxt<'cx, 'tcx>,
        allow_negative_impls: bool,
    ) -> SelectionContext<'cx, 'tcx> {
        debug!(?allow_negative_impls, "with_negative");
        SelectionContext {
            infcx,
            freshener: infcx.freshener(),
            intercrate: false,
            intercrate_ambiguity_causes: None,
            allow_negative_impls,
            query_mode: TraitQueryMode::Standard,
        }
    }

    pub fn with_query_mode(
        infcx: &'cx InferCtxt<'cx, 'tcx>,
        query_mode: TraitQueryMode,
    ) -> SelectionContext<'cx, 'tcx> {
        debug!(?query_mode, "with_query_mode");
        SelectionContext {
            infcx,
            freshener: infcx.freshener(),
            intercrate: false,
            intercrate_ambiguity_causes: None,
            allow_negative_impls: false,
            query_mode,
        }
    }

    /// Enables tracking of intercrate ambiguity causes. These are
    /// used in coherence to give improved diagnostics. We don't do
    /// this until we detect a coherence error because it can lead to
    /// false overflow results (#47139) and because it costs
    /// computation time.
    pub fn enable_tracking_intercrate_ambiguity_causes(&mut self) {
        assert!(self.intercrate);
        assert!(self.intercrate_ambiguity_causes.is_none());
        self.intercrate_ambiguity_causes = Some(vec![]);
        debug!("selcx: enable_tracking_intercrate_ambiguity_causes");
    }

    /// Gets the intercrate ambiguity causes collected since tracking
    /// was enabled and disables tracking at the same time. If
    /// tracking is not enabled, just returns an empty vector.
    pub fn take_intercrate_ambiguity_causes(&mut self) -> Vec<IntercrateAmbiguityCause> {
        assert!(self.intercrate);
        self.intercrate_ambiguity_causes.take().unwrap_or_default()
    }

    pub fn infcx(&self) -> &'cx InferCtxt<'cx, 'tcx> {
        self.infcx
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
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
    //    is `Vec<Foo>: Iterable<Bar>`, but the impl specifies
    //    `impl<T> Iterable<T> for Vec<T>`, than an error would result.

    /// Attempts to satisfy the obligation. If successful, this will affect the surrounding
    /// type environment by performing unification.
    #[instrument(level = "debug", skip(self))]
    pub fn select(
        &mut self,
        obligation: &TraitObligation<'tcx>,
    ) -> SelectionResult<'tcx, Selection<'tcx>> {
        debug_assert!(!obligation.predicate.has_escaping_bound_vars());

        let pec = &ProvisionalEvaluationCache::default();
        let stack = self.push_stack(TraitObligationStackList::empty(pec), obligation);

        let candidate = match self.candidate_from_obligation(&stack) {
            Err(SelectionError::Overflow) => {
                // In standard mode, overflow must have been caught and reported
                // earlier.
                assert!(self.query_mode == TraitQueryMode::Canonical);
                return Err(SelectionError::Overflow);
            }
            Err(e) => {
                return Err(e);
            }
            Ok(None) => {
                return Ok(None);
            }
            Ok(Some(candidate)) => candidate,
        };

        match self.confirm_candidate(obligation, candidate) {
            Err(SelectionError::Overflow) => {
                assert!(self.query_mode == TraitQueryMode::Canonical);
                Err(SelectionError::Overflow)
            }
            Err(e) => Err(e),
            Ok(candidate) => {
                debug!(?candidate);
                Ok(Some(candidate))
            }
        }
    }

    ///////////////////////////////////////////////////////////////////////////
    // EVALUATION
    //
    // Tests whether an obligation can be selected or whether an impl
    // can be applied to particular types. It skips the "confirmation"
    // step and hence completely ignores output type parameters.
    //
    // The result is "true" if the obligation *may* hold and "false" if
    // we can be sure it does not.

    /// Evaluates whether the obligation `obligation` can be satisfied (by any means).
    pub fn predicate_may_hold_fatal(&mut self, obligation: &PredicateObligation<'tcx>) -> bool {
        debug!(?obligation, "predicate_may_hold_fatal");

        // This fatal query is a stopgap that should only be used in standard mode,
        // where we do not expect overflow to be propagated.
        assert!(self.query_mode == TraitQueryMode::Standard);

        self.evaluate_root_obligation(obligation)
            .expect("Overflow should be caught earlier in standard query mode")
            .may_apply()
    }

    /// Evaluates whether the obligation `obligation` can be satisfied
    /// and returns an `EvaluationResult`. This is meant for the
    /// *initial* call.
    pub fn evaluate_root_obligation(
        &mut self,
        obligation: &PredicateObligation<'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        self.evaluation_probe(|this| {
            this.evaluate_predicate_recursively(
                TraitObligationStackList::empty(&ProvisionalEvaluationCache::default()),
                obligation.clone(),
            )
        })
    }

    fn evaluation_probe(
        &mut self,
        op: impl FnOnce(&mut Self) -> Result<EvaluationResult, OverflowError>,
    ) -> Result<EvaluationResult, OverflowError> {
        self.infcx.probe(|snapshot| -> Result<EvaluationResult, OverflowError> {
            let result = op(self)?;

            match self.infcx.leak_check(true, snapshot) {
                Ok(()) => {}
                Err(_) => return Ok(EvaluatedToErr),
            }

            match self.infcx.region_constraints_added_in_snapshot(snapshot) {
                None => Ok(result),
                Some(_) => Ok(result.max(EvaluatedToOkModuloRegions)),
            }
        })
    }

    /// Evaluates the predicates in `predicates` recursively. Note that
    /// this applies projections in the predicates, and therefore
    /// is run within an inference probe.
    fn evaluate_predicates_recursively<'o, I>(
        &mut self,
        stack: TraitObligationStackList<'o, 'tcx>,
        predicates: I,
    ) -> Result<EvaluationResult, OverflowError>
    where
        I: IntoIterator<Item = PredicateObligation<'tcx>> + std::fmt::Debug,
    {
        let mut result = EvaluatedToOk;
        debug!(?predicates, "evaluate_predicates_recursively");
        for obligation in predicates {
            let eval = self.evaluate_predicate_recursively(stack, obligation.clone())?;
            if let EvaluatedToErr = eval {
                // fast-path - EvaluatedToErr is the top of the lattice,
                // so we don't need to look on the other predicates.
                return Ok(EvaluatedToErr);
            } else {
                result = cmp::max(result, eval);
            }
        }
        Ok(result)
    }

    #[instrument(
        level = "debug",
        skip(self, previous_stack),
        fields(previous_stack = ?previous_stack)
    )]
    fn evaluate_predicate_recursively<'o>(
        &mut self,
        previous_stack: TraitObligationStackList<'o, 'tcx>,
        obligation: PredicateObligation<'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        // `previous_stack` stores a `TraitObligation`, while `obligation` is
        // a `PredicateObligation`. These are distinct types, so we can't
        // use any `Option` combinator method that would force them to be
        // the same.
        match previous_stack.head() {
            Some(h) => self.check_recursion_limit(&obligation, h.obligation)?,
            None => self.check_recursion_limit(&obligation, &obligation)?,
        }

        let result = ensure_sufficient_stack(|| {
            let bound_predicate = obligation.predicate.kind();
            match bound_predicate.skip_binder() {
                ty::PredicateKind::Trait(t, _) => {
                    let t = bound_predicate.rebind(t);
                    debug_assert!(!t.has_escaping_bound_vars());
                    let obligation = obligation.with(t);
                    self.evaluate_trait_predicate_recursively(previous_stack, obligation)
                }

                ty::PredicateKind::Subtype(p) => {
                    let p = bound_predicate.rebind(p);
                    // Does this code ever run?
                    match self.infcx.subtype_predicate(&obligation.cause, obligation.param_env, p) {
                        Some(Ok(InferOk { mut obligations, .. })) => {
                            self.add_depth(obligations.iter_mut(), obligation.recursion_depth);
                            self.evaluate_predicates_recursively(
                                previous_stack,
                                obligations.into_iter(),
                            )
                        }
                        Some(Err(_)) => Ok(EvaluatedToErr),
                        None => Ok(EvaluatedToAmbig),
                    }
                }

                ty::PredicateKind::WellFormed(arg) => match wf::obligations(
                    self.infcx,
                    obligation.param_env,
                    obligation.cause.body_id,
                    obligation.recursion_depth + 1,
                    arg,
                    obligation.cause.span,
                ) {
                    Some(mut obligations) => {
                        self.add_depth(obligations.iter_mut(), obligation.recursion_depth);
                        self.evaluate_predicates_recursively(previous_stack, obligations)
                    }
                    None => Ok(EvaluatedToAmbig),
                },

                ty::PredicateKind::TypeOutlives(..) | ty::PredicateKind::RegionOutlives(..) => {
                    // We do not consider region relationships when evaluating trait matches.
                    Ok(EvaluatedToOkModuloRegions)
                }

                ty::PredicateKind::ObjectSafe(trait_def_id) => {
                    if self.tcx().is_object_safe(trait_def_id) {
                        Ok(EvaluatedToOk)
                    } else {
                        Ok(EvaluatedToErr)
                    }
                }

                ty::PredicateKind::Projection(data) => {
                    let data = bound_predicate.rebind(data);
                    let project_obligation = obligation.with(data);
                    match project::poly_project_and_unify_type(self, &project_obligation) {
                        Ok(Ok(Some(mut subobligations))) => {
                            self.add_depth(subobligations.iter_mut(), obligation.recursion_depth);
                            let result = self
                                .evaluate_predicates_recursively(previous_stack, subobligations);
                            if let Some(key) =
                                ProjectionCacheKey::from_poly_projection_predicate(self, data)
                            {
                                self.infcx.inner.borrow_mut().projection_cache().complete(key);
                            }
                            result
                        }
                        Ok(Ok(None)) => Ok(EvaluatedToAmbig),
                        Ok(Err(project::InProgress)) => Ok(EvaluatedToRecur),
                        Err(_) => Ok(EvaluatedToErr),
                    }
                }

                ty::PredicateKind::ClosureKind(_, closure_substs, kind) => {
                    match self.infcx.closure_kind(closure_substs) {
                        Some(closure_kind) => {
                            if closure_kind.extends(kind) {
                                Ok(EvaluatedToOk)
                            } else {
                                Ok(EvaluatedToErr)
                            }
                        }
                        None => Ok(EvaluatedToAmbig),
                    }
                }

                ty::PredicateKind::ConstEvaluatable(def_id, substs) => {
                    match const_evaluatable::is_const_evaluatable(
                        self.infcx,
                        def_id,
                        substs,
                        obligation.param_env,
                        obligation.cause.span,
                    ) {
                        Ok(()) => Ok(EvaluatedToOk),
                        Err(NotConstEvaluatable::MentionsInfer) => Ok(EvaluatedToAmbig),
                        Err(NotConstEvaluatable::MentionsParam) => Ok(EvaluatedToErr),
                        Err(_) => Ok(EvaluatedToErr),
                    }
                }

                ty::PredicateKind::ConstEquate(c1, c2) => {
                    debug!(?c1, ?c2, "evaluate_predicate_recursively: equating consts");

                    let evaluate = |c: &'tcx ty::Const<'tcx>| {
                        if let ty::ConstKind::Unevaluated(unevaluated) = c.val {
                            self.infcx
                                .const_eval_resolve(
                                    obligation.param_env,
                                    unevaluated,
                                    Some(obligation.cause.span),
                                )
                                .map(|val| ty::Const::from_value(self.tcx(), val, c.ty))
                        } else {
                            Ok(c)
                        }
                    };

                    match (evaluate(c1), evaluate(c2)) {
                        (Ok(c1), Ok(c2)) => {
                            match self
                                .infcx()
                                .at(&obligation.cause, obligation.param_env)
                                .eq(c1, c2)
                            {
                                Ok(_) => Ok(EvaluatedToOk),
                                Err(_) => Ok(EvaluatedToErr),
                            }
                        }
                        (Err(ErrorHandled::Reported(ErrorReported)), _)
                        | (_, Err(ErrorHandled::Reported(ErrorReported))) => Ok(EvaluatedToErr),
                        (Err(ErrorHandled::Linted), _) | (_, Err(ErrorHandled::Linted)) => {
                            span_bug!(
                                obligation.cause.span(self.tcx()),
                                "ConstEquate: const_eval_resolve returned an unexpected error"
                            )
                        }
                        (Err(ErrorHandled::TooGeneric), _) | (_, Err(ErrorHandled::TooGeneric)) => {
                            Ok(EvaluatedToAmbig)
                        }
                    }
                }
                ty::PredicateKind::TypeWellFormedFromEnv(..) => {
                    bug!("TypeWellFormedFromEnv is only used for chalk")
                }
            }
        });

        debug!(?result);

        result
    }

    fn evaluate_trait_predicate_recursively<'o>(
        &mut self,
        previous_stack: TraitObligationStackList<'o, 'tcx>,
        mut obligation: TraitObligation<'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        debug!(?obligation, "evaluate_trait_predicate_recursively");

        if !self.intercrate
            && obligation.is_global()
            && obligation.param_env.caller_bounds().iter().all(|bound| bound.needs_subst())
        {
            // If a param env has no global bounds, global obligations do not
            // depend on its particular value in order to work, so we can clear
            // out the param env and get better caching.
            debug!("evaluate_trait_predicate_recursively - in global");
            obligation.param_env = obligation.param_env.without_caller_bounds();
        }

        let stack = self.push_stack(previous_stack, &obligation);
        let fresh_trait_ref = stack.fresh_trait_ref;

        debug!(?fresh_trait_ref);

        if let Some(result) = self.check_evaluation_cache(obligation.param_env, fresh_trait_ref) {
            debug!(?result, "CACHE HIT");
            return Ok(result);
        }

        if let Some(result) = stack.cache().get_provisional(fresh_trait_ref) {
            debug!(?result, "PROVISIONAL CACHE HIT");
            stack.update_reached_depth(result.reached_depth);
            return Ok(result.result);
        }

        // Check if this is a match for something already on the
        // stack. If so, we don't want to insert the result into the
        // main cache (it is cycle dependent) nor the provisional
        // cache (which is meant for things that have completed but
        // for a "backedge" -- this result *is* the backedge).
        if let Some(cycle_result) = self.check_evaluation_cycle(&stack) {
            return Ok(cycle_result);
        }

        let (result, dep_node) = self.in_task(|this| this.evaluate_stack(&stack));
        let result = result?;

        if !result.must_apply_modulo_regions() {
            stack.cache().on_failure(stack.dfn);
        }

        let reached_depth = stack.reached_depth.get();
        if reached_depth >= stack.depth {
            debug!(?result, "CACHE MISS");
            self.insert_evaluation_cache(obligation.param_env, fresh_trait_ref, dep_node, result);

            stack.cache().on_completion(stack.dfn, |fresh_trait_ref, provisional_result| {
                self.insert_evaluation_cache(
                    obligation.param_env,
                    fresh_trait_ref,
                    dep_node,
                    provisional_result.max(result),
                );
            });
        } else {
            debug!(?result, "PROVISIONAL");
            debug!(
                "evaluate_trait_predicate_recursively: caching provisionally because {:?} \
                 is a cycle participant (at depth {}, reached depth {})",
                fresh_trait_ref, stack.depth, reached_depth,
            );

            stack.cache().insert_provisional(stack.dfn, reached_depth, fresh_trait_ref, result);
        }

        Ok(result)
    }

    /// If there is any previous entry on the stack that precisely
    /// matches this obligation, then we can assume that the
    /// obligation is satisfied for now (still all other conditions
    /// must be met of course). One obvious case this comes up is
    /// marker traits like `Send`. Think of a linked list:
    ///
    ///    struct List<T> { data: T, next: Option<Box<List<T>>> }
    ///
    /// `Box<List<T>>` will be `Send` if `T` is `Send` and
    /// `Option<Box<List<T>>>` is `Send`, and in turn
    /// `Option<Box<List<T>>>` is `Send` if `Box<List<T>>` is
    /// `Send`.
    ///
    /// Note that we do this comparison using the `fresh_trait_ref`
    /// fields. Because these have all been freshened using
    /// `self.freshener`, we can be sure that (a) this will not
    /// affect the inferencer state and (b) that if we see two
    /// fresh regions with the same index, they refer to the same
    /// unbound type variable.
    fn check_evaluation_cycle(
        &mut self,
        stack: &TraitObligationStack<'_, 'tcx>,
    ) -> Option<EvaluationResult> {
        if let Some(cycle_depth) = stack
            .iter()
            .skip(1) // Skip top-most frame.
            .find(|prev| {
                stack.obligation.param_env == prev.obligation.param_env
                    && stack.fresh_trait_ref == prev.fresh_trait_ref
            })
            .map(|stack| stack.depth)
        {
            let cycle = || stack.iter().skip(1).take_while(|s| s.depth >= cycle_depth);
            debug!(
                "check_evaluation_cycle: recursive at depth {} from depth {} dfn {}, cycle={:#?}, rest of stack={:#?}",
                cycle_depth,
                stack.depth,
                stack.dfn,
                cycle().collect::<Vec<_>>(),
                stack.iter().skip_while(|s| s.depth >= cycle_depth).collect::<Vec<_>>(),
            );

            // If we have a stack like `A B C D E A`, where the top of
            // the stack is the final `A`, then this will iterate over
            // `A, E, D, C, B` -- i.e., all the participants apart
            // from the cycle head. We mark them as participating in a
            // cycle. This suppresses caching for those nodes. See
            // `in_cycle` field for more details.
            stack.update_reached_depth(cycle_depth);

            // Subtle: when checking for a coinductive cycle, we do
            // not compare using the "freshened trait refs" (which
            // have erased regions) but rather the fully explicit
            // trait refs. This is important because it's only a cycle
            // if the regions match exactly.
            let tcx = self.tcx();
            let cycle =
                cycle().map(|stack| stack.obligation.predicate.without_const().to_predicate(tcx));
            if self.coinductive_match(cycle) {
                debug!("evaluate_stack --> recursive, coinductive");
                Some(EvaluatedToOk)
            } else {
                debug!("evaluate_stack --> recursive, inductive");
                Some(EvaluatedToRecur)
            }
        } else {
            None
        }
    }

    fn evaluate_stack<'o>(
        &mut self,
        stack: &TraitObligationStack<'o, 'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        // In intercrate mode, whenever any of the generics are unbound,
        // there can always be an impl. Even if there are no impls in
        // this crate, perhaps the type would be unified with
        // something from another crate that does provide an impl.
        //
        // In intra mode, we must still be conservative. The reason is
        // that we want to avoid cycles. Imagine an impl like:
        //
        //     impl<T:Eq> Eq for Vec<T>
        //
        // and a trait reference like `$0 : Eq` where `$0` is an
        // unbound variable. When we evaluate this trait-reference, we
        // will unify `$0` with `Vec<$1>` (for some fresh variable
        // `$1`), on the condition that `$1 : Eq`. We will then wind
        // up with many candidates (since that are other `Eq` impls
        // that apply) and try to winnow things down. This results in
        // a recursive evaluation that `$1 : Eq` -- as you can
        // imagine, this is just where we started. To avoid that, we
        // check for unbound variables and return an ambiguous (hence possible)
        // match if we've seen this trait before.
        //
        // This suffices to allow chains like `FnMut` implemented in
        // terms of `Fn` etc, but we could probably make this more
        // precise still.
        let unbound_input_types =
            stack.fresh_trait_ref.skip_binder().substs.types().any(|ty| ty.is_fresh());
        // This check was an imperfect workaround for a bug in the old
        // intercrate mode; it should be removed when that goes away.
        if unbound_input_types && self.intercrate {
            debug!("evaluate_stack --> unbound argument, intercrate -->  ambiguous",);
            // Heuristics: show the diagnostics when there are no candidates in crate.
            if self.intercrate_ambiguity_causes.is_some() {
                debug!("evaluate_stack: intercrate_ambiguity_causes is some");
                if let Ok(candidate_set) = self.assemble_candidates(stack) {
                    if !candidate_set.ambiguous && candidate_set.vec.is_empty() {
                        let trait_ref = stack.obligation.predicate.skip_binder().trait_ref;
                        let self_ty = trait_ref.self_ty();
                        let cause =
                            with_no_trimmed_paths(|| IntercrateAmbiguityCause::DownstreamCrate {
                                trait_desc: trait_ref.print_only_trait_path().to_string(),
                                self_desc: if self_ty.has_concrete_skeleton() {
                                    Some(self_ty.to_string())
                                } else {
                                    None
                                },
                            });

                        debug!(?cause, "evaluate_stack: pushing cause");
                        self.intercrate_ambiguity_causes.as_mut().unwrap().push(cause);
                    }
                }
            }
            return Ok(EvaluatedToAmbig);
        }
        if unbound_input_types
            && stack.iter().skip(1).any(|prev| {
                stack.obligation.param_env == prev.obligation.param_env
                    && self.match_fresh_trait_refs(
                        stack.fresh_trait_ref,
                        prev.fresh_trait_ref,
                        prev.obligation.param_env,
                    )
            })
        {
            debug!("evaluate_stack --> unbound argument, recursive --> giving up",);
            return Ok(EvaluatedToUnknown);
        }

        match self.candidate_from_obligation(stack) {
            Ok(Some(c)) => self.evaluate_candidate(stack, &c),
            Ok(None) => Ok(EvaluatedToAmbig),
            Err(Overflow) => Err(OverflowError),
            Err(..) => Ok(EvaluatedToErr),
        }
    }

    /// For defaulted traits, we use a co-inductive strategy to solve, so
    /// that recursion is ok. This routine returns `true` if the top of the
    /// stack (`cycle[0]`):
    ///
    /// - is a defaulted trait,
    /// - it also appears in the backtrace at some position `X`,
    /// - all the predicates at positions `X..` between `X` and the top are
    ///   also defaulted traits.
    pub fn coinductive_match<I>(&mut self, mut cycle: I) -> bool
    where
        I: Iterator<Item = ty::Predicate<'tcx>>,
    {
        cycle.all(|predicate| self.coinductive_predicate(predicate))
    }

    fn coinductive_predicate(&self, predicate: ty::Predicate<'tcx>) -> bool {
        let result = match predicate.kind().skip_binder() {
            ty::PredicateKind::Trait(ref data, _) => self.tcx().trait_is_auto(data.def_id()),
            _ => false,
        };
        debug!(?predicate, ?result, "coinductive_predicate");
        result
    }

    /// Further evaluates `candidate` to decide whether all type parameters match and whether nested
    /// obligations are met. Returns whether `candidate` remains viable after this further
    /// scrutiny.
    #[instrument(
        level = "debug",
        skip(self, stack),
        fields(depth = stack.obligation.recursion_depth)
    )]
    fn evaluate_candidate<'o>(
        &mut self,
        stack: &TraitObligationStack<'o, 'tcx>,
        candidate: &SelectionCandidate<'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        let mut result = self.evaluation_probe(|this| {
            let candidate = (*candidate).clone();
            match this.confirm_candidate(stack.obligation, candidate) {
                Ok(selection) => {
                    debug!(?selection);
                    this.evaluate_predicates_recursively(
                        stack.list(),
                        selection.nested_obligations().into_iter(),
                    )
                }
                Err(..) => Ok(EvaluatedToErr),
            }
        })?;

        // If we erased any lifetimes, then we want to use
        // `EvaluatedToOkModuloRegions` instead of `EvaluatedToOk`
        // as your final result. The result will be cached using
        // the freshened trait predicate as a key, so we need
        // our result to be correct by *any* choice of original lifetimes,
        // not just the lifetime choice for this particular (non-erased)
        // predicate.
        // See issue #80691
        if stack.fresh_trait_ref.has_erased_regions() {
            result = result.max(EvaluatedToOkModuloRegions);
        }

        debug!(?result);
        Ok(result)
    }

    fn check_evaluation_cache(
        &self,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref: ty::PolyTraitRef<'tcx>,
    ) -> Option<EvaluationResult> {
        let tcx = self.tcx();
        let key = param_env.and(trait_ref);
        if self.can_use_global_caches(param_env) {
            if let Some(res) = tcx.evaluation_cache.get(&key, tcx) {
                debug!(?key, ?res, "check_evaluation_cache global");
                return Some(res);
            }
        }
        if let Some(res) = self.infcx.evaluation_cache.get(&key, tcx) {
            debug!(?key, ?res, "check_evaluation_cache");
            Some(res)
        } else {
            None
        }
    }

    fn insert_evaluation_cache(
        &mut self,
        param_env: ty::ParamEnv<'tcx>,
        trait_ref: ty::PolyTraitRef<'tcx>,
        dep_node: DepNodeIndex,
        result: EvaluationResult,
    ) {
        // Avoid caching results that depend on more than just the trait-ref
        // - the stack can create recursion.
        if result.is_stack_dependent() {
            return;
        }

        let key = param_env.and(trait_ref);

        if self.can_use_global_caches(param_env) {
            if !trait_ref.needs_infer() {
                debug!(?key, ?result, "insert_evaluation_cache global");
                debug!("insert_evaluation_cache global cache={:?}", self.tcx().evaluation_cache);
                // This may overwrite the cache with the same value
                // FIXME: Due to #50507 this overwrites the different values
                // This should be changed to use HashMapExt::insert_same
                // when that is fixed
                self.tcx().evaluation_cache.insert(key, dep_node, result);
                return;
            }
        }

        debug!(?key, ?result, "insert_evaluation_cache");
        debug!("insert_evaluation_cache cache={:?}", self.infcx.evaluation_cache);
        self.infcx.evaluation_cache.insert(key, dep_node, result);
    }

    /// For various reasons, it's possible for a subobligation
    /// to have a *lower* recursion_depth than the obligation used to create it.
    /// Projection sub-obligations may be returned from the projection cache,
    /// which results in obligations with an 'old' `recursion_depth`.
    /// Additionally, methods like `InferCtxt.subtype_predicate` produce
    /// subobligations without taking in a 'parent' depth, causing the
    /// generated subobligations to have a `recursion_depth` of `0`.
    ///
    /// To ensure that obligation_depth never decreases, we force all subobligations
    /// to have at least the depth of the original obligation.
    fn add_depth<T: 'cx, I: Iterator<Item = &'cx mut Obligation<'tcx, T>>>(
        &self,
        it: I,
        min_depth: usize,
    ) {
        it.for_each(|o| o.recursion_depth = cmp::max(min_depth, o.recursion_depth) + 1);
    }

    /// Checks that the recursion limit has not been exceeded.
    ///
    /// The weird return type of this function allows it to be used with the `try` (`?`)
    /// operator within certain functions.
    fn check_recursion_limit<T: Display + TypeFoldable<'tcx>, V: Display + TypeFoldable<'tcx>>(
        &self,
        obligation: &Obligation<'tcx, T>,
        error_obligation: &Obligation<'tcx, V>,
    ) -> Result<(), OverflowError> {
        if !self.infcx.tcx.sess.recursion_limit().value_within_limit(obligation.recursion_depth) {
            match self.query_mode {
                TraitQueryMode::Standard => {
                    self.infcx().report_overflow_error(error_obligation, true);
                }
                TraitQueryMode::Canonical => {
                    return Err(OverflowError);
                }
            }
        }
        Ok(())
    }

    fn in_task<OP, R>(&mut self, op: OP) -> (R, DepNodeIndex)
    where
        OP: FnOnce(&mut Self) -> R,
    {
        let (result, dep_node) =
            self.tcx().dep_graph.with_anon_task(self.tcx(), DepKind::TraitSelect, || op(self));
        self.tcx().dep_graph.read_index(dep_node);
        (result, dep_node)
    }

    // Treat negative impls as unimplemented, and reservation impls as ambiguity.
    fn filter_negative_and_reservation_impls(
        &mut self,
        candidate: SelectionCandidate<'tcx>,
    ) -> SelectionResult<'tcx, SelectionCandidate<'tcx>> {
        if let ImplCandidate(def_id) = candidate {
            let tcx = self.tcx();
            match tcx.impl_polarity(def_id) {
                ty::ImplPolarity::Negative if !self.allow_negative_impls => {
                    return Err(Unimplemented);
                }
                ty::ImplPolarity::Reservation => {
                    if let Some(intercrate_ambiguity_clauses) =
                        &mut self.intercrate_ambiguity_causes
                    {
                        let attrs = tcx.get_attrs(def_id);
                        let attr = tcx.sess.find_by_name(&attrs, sym::rustc_reservation_impl);
                        let value = attr.and_then(|a| a.value_str());
                        if let Some(value) = value {
                            debug!(
                                "filter_negative_and_reservation_impls: \
                                 reservation impl ambiguity on {:?}",
                                def_id
                            );
                            intercrate_ambiguity_clauses.push(
                                IntercrateAmbiguityCause::ReservationImpl {
                                    message: value.to_string(),
                                },
                            );
                        }
                    }
                    return Ok(None);
                }
                _ => {}
            };
        }
        Ok(Some(candidate))
    }

    fn is_knowable<'o>(&mut self, stack: &TraitObligationStack<'o, 'tcx>) -> Option<Conflict> {
        debug!("is_knowable(intercrate={:?})", self.intercrate);

        if !self.intercrate {
            return None;
        }

        let obligation = &stack.obligation;
        let predicate = self.infcx().resolve_vars_if_possible(obligation.predicate);

        // Okay to skip binder because of the nature of the
        // trait-ref-is-knowable check, which does not care about
        // bound regions.
        let trait_ref = predicate.skip_binder().trait_ref;

        coherence::trait_ref_is_knowable(self.tcx(), trait_ref)
    }

    /// Returns `true` if the global caches can be used.
    fn can_use_global_caches(&self, param_env: ty::ParamEnv<'tcx>) -> bool {
        // If there are any inference variables in the `ParamEnv`, then we
        // always use a cache local to this particular scope. Otherwise, we
        // switch to a global cache.
        if param_env.needs_infer() {
            return false;
        }

        // Avoid using the master cache during coherence and just rely
        // on the local cache. This effectively disables caching
        // during coherence. It is really just a simplification to
        // avoid us having to fear that coherence results "pollute"
        // the master cache. Since coherence executes pretty quickly,
        // it's not worth going to more trouble to increase the
        // hit-rate, I don't think.
        if self.intercrate {
            return false;
        }

        // Otherwise, we can use the global cache.
        true
    }

    fn check_candidate_cache(
        &mut self,
        param_env: ty::ParamEnv<'tcx>,
        cache_fresh_trait_pred: ty::PolyTraitPredicate<'tcx>,
    ) -> Option<SelectionResult<'tcx, SelectionCandidate<'tcx>>> {
        let tcx = self.tcx();
        let trait_ref = &cache_fresh_trait_pred.skip_binder().trait_ref;
        if self.can_use_global_caches(param_env) {
            if let Some(res) = tcx.selection_cache.get(&param_env.and(*trait_ref), tcx) {
                return Some(res);
            }
        }
        self.infcx.selection_cache.get(&param_env.and(*trait_ref), tcx)
    }

    /// Determines whether can we safely cache the result
    /// of selecting an obligation. This is almost always `true`,
    /// except when dealing with certain `ParamCandidate`s.
    ///
    /// Ordinarily, a `ParamCandidate` will contain no inference variables,
    /// since it was usually produced directly from a `DefId`. However,
    /// certain cases (currently only librustdoc's blanket impl finder),
    /// a `ParamEnv` may be explicitly constructed with inference types.
    /// When this is the case, we do *not* want to cache the resulting selection
    /// candidate. This is due to the fact that it might not always be possible
    /// to equate the obligation's trait ref and the candidate's trait ref,
    /// if more constraints end up getting added to an inference variable.
    ///
    /// Because of this, we always want to re-run the full selection
    /// process for our obligation the next time we see it, since
    /// we might end up picking a different `SelectionCandidate` (or none at all).
    fn can_cache_candidate(
        &self,
        result: &SelectionResult<'tcx, SelectionCandidate<'tcx>>,
    ) -> bool {
        match result {
            Ok(Some(SelectionCandidate::ParamCandidate(trait_ref))) => !trait_ref.needs_infer(),
            _ => true,
        }
    }

    fn insert_candidate_cache(
        &mut self,
        param_env: ty::ParamEnv<'tcx>,
        cache_fresh_trait_pred: ty::PolyTraitPredicate<'tcx>,
        dep_node: DepNodeIndex,
        candidate: SelectionResult<'tcx, SelectionCandidate<'tcx>>,
    ) {
        let tcx = self.tcx();
        let trait_ref = cache_fresh_trait_pred.skip_binder().trait_ref;

        if !self.can_cache_candidate(&candidate) {
            debug!(?trait_ref, ?candidate, "insert_candidate_cache - candidate is not cacheable");
            return;
        }

        if self.can_use_global_caches(param_env) {
            if let Err(Overflow) = candidate {
                // Don't cache overflow globally; we only produce this in certain modes.
            } else if !trait_ref.needs_infer() {
                if !candidate.needs_infer() {
                    debug!(?trait_ref, ?candidate, "insert_candidate_cache global");
                    // This may overwrite the cache with the same value.
                    tcx.selection_cache.insert(param_env.and(trait_ref), dep_node, candidate);
                    return;
                }
            }
        }

        debug!(?trait_ref, ?candidate, "insert_candidate_cache local");
        self.infcx.selection_cache.insert(param_env.and(trait_ref), dep_node, candidate);
    }

    /// Matches a predicate against the bounds of its self type.
    ///
    /// Given an obligation like `<T as Foo>::Bar: Baz` where the self type is
    /// a projection, look at the bounds of `T::Bar`, see if we can find a
    /// `Baz` bound. We return indexes into the list returned by
    /// `tcx.item_bounds` for any applicable bounds.
    fn match_projection_obligation_against_definition_bounds(
        &mut self,
        obligation: &TraitObligation<'tcx>,
    ) -> smallvec::SmallVec<[usize; 2]> {
        let poly_trait_predicate = self.infcx().resolve_vars_if_possible(obligation.predicate);
        let placeholder_trait_predicate =
            self.infcx().replace_bound_vars_with_placeholders(poly_trait_predicate);
        debug!(
            ?placeholder_trait_predicate,
            "match_projection_obligation_against_definition_bounds"
        );

        let tcx = self.infcx.tcx;
        let (def_id, substs) = match *placeholder_trait_predicate.trait_ref.self_ty().kind() {
            ty::Projection(ref data) => (data.item_def_id, data.substs),
            ty::Opaque(def_id, substs) => (def_id, substs),
            _ => {
                span_bug!(
                    obligation.cause.span,
                    "match_projection_obligation_against_definition_bounds() called \
                     but self-ty is not a projection: {:?}",
                    placeholder_trait_predicate.trait_ref.self_ty()
                );
            }
        };
        let bounds = tcx.item_bounds(def_id).subst(tcx, substs);

        // The bounds returned by `item_bounds` may contain duplicates after
        // normalization, so try to deduplicate when possible to avoid
        // unnecessary ambiguity.
        let mut distinct_normalized_bounds = FxHashSet::default();

        let matching_bounds = bounds
            .iter()
            .enumerate()
            .filter_map(|(idx, bound)| {
                let bound_predicate = bound.kind();
                if let ty::PredicateKind::Trait(pred, _) = bound_predicate.skip_binder() {
                    let bound = bound_predicate.rebind(pred.trait_ref);
                    if self.infcx.probe(|_| {
                        match self.match_normalize_trait_ref(
                            obligation,
                            bound,
                            placeholder_trait_predicate.trait_ref,
                        ) {
                            Ok(None) => true,
                            Ok(Some(normalized_trait))
                                if distinct_normalized_bounds.insert(normalized_trait) =>
                            {
                                true
                            }
                            _ => false,
                        }
                    }) {
                        return Some(idx);
                    }
                }
                None
            })
            .collect();

        debug!(?matching_bounds, "match_projection_obligation_against_definition_bounds");
        matching_bounds
    }

    /// Equates the trait in `obligation` with trait bound. If the two traits
    /// can be equated and the normalized trait bound doesn't contain inference
    /// variables or placeholders, the normalized bound is returned.
    fn match_normalize_trait_ref(
        &mut self,
        obligation: &TraitObligation<'tcx>,
        trait_bound: ty::PolyTraitRef<'tcx>,
        placeholder_trait_ref: ty::TraitRef<'tcx>,
    ) -> Result<Option<ty::PolyTraitRef<'tcx>>, ()> {
        debug_assert!(!placeholder_trait_ref.has_escaping_bound_vars());
        if placeholder_trait_ref.def_id != trait_bound.def_id() {
            // Avoid unnecessary normalization
            return Err(());
        }

        let Normalized { value: trait_bound, obligations: _ } = ensure_sufficient_stack(|| {
            project::normalize_with_depth(
                self,
                obligation.param_env,
                obligation.cause.clone(),
                obligation.recursion_depth + 1,
                trait_bound,
            )
        });
        self.infcx
            .at(&obligation.cause, obligation.param_env)
            .sup(ty::Binder::dummy(placeholder_trait_ref), trait_bound)
            .map(|InferOk { obligations: _, value: () }| {
                // This method is called within a probe, so we can't have
                // inference variables and placeholders escape.
                if !trait_bound.needs_infer() && !trait_bound.has_placeholders() {
                    Some(trait_bound)
                } else {
                    None
                }
            })
            .map_err(|_| ())
    }

    fn evaluate_where_clause<'o>(
        &mut self,
        stack: &TraitObligationStack<'o, 'tcx>,
        where_clause_trait_ref: ty::PolyTraitRef<'tcx>,
    ) -> Result<EvaluationResult, OverflowError> {
        self.evaluation_probe(|this| {
            match this.match_where_clause_trait_ref(stack.obligation, where_clause_trait_ref) {
                Ok(obligations) => this.evaluate_predicates_recursively(stack.list(), obligations),
                Err(()) => Ok(EvaluatedToErr),
            }
        })
    }

    pub(super) fn match_projection_projections(
        &mut self,
        obligation: &ProjectionTyObligation<'tcx>,
        env_predicate: PolyProjectionPredicate<'tcx>,
        potentially_unnormalized_candidates: bool,
    ) -> bool {
        let mut nested_obligations = Vec::new();
        let (infer_predicate, _) = self.infcx.replace_bound_vars_with_fresh_vars(
            obligation.cause.span,
            LateBoundRegionConversionTime::HigherRankedType,
            env_predicate,
        );
        let infer_projection = if potentially_unnormalized_candidates {
            ensure_sufficient_stack(|| {
                project::normalize_with_depth_to(
                    self,
                    obligation.param_env,
                    obligation.cause.clone(),
                    obligation.recursion_depth + 1,
                    infer_predicate.projection_ty,
                    &mut nested_obligations,
                )
            })
        } else {
            infer_predicate.projection_ty
        };

        self.infcx
            .at(&obligation.cause, obligation.param_env)
            .sup(obligation.predicate, infer_projection)
            .map_or(false, |InferOk { obligations, value: () }| {
                self.evaluate_predicates_recursively(
                    TraitObligationStackList::empty(&ProvisionalEvaluationCache::default()),
                    nested_obligations.into_iter().chain(obligations),
                )
                .map_or(false, |res| res.may_apply())
            })
    }

    ///////////////////////////////////////////////////////////////////////////
    // WINNOW
    //
    // Winnowing is the process of attempting to resolve ambiguity by
    // probing further. During the winnowing process, we unify all
    // type variables and then we also attempt to evaluate recursive
    // bounds to see if they are satisfied.

    /// Returns `true` if `victim` should be dropped in favor of
    /// `other`. Generally speaking we will drop duplicate
    /// candidates and prefer where-clause candidates.
    ///
    /// See the comment for "SelectionCandidate" for more details.
    fn candidate_should_be_dropped_in_favor_of(
        &mut self,
        victim: &EvaluatedCandidate<'tcx>,
        other: &EvaluatedCandidate<'tcx>,
        needs_infer: bool,
    ) -> bool {
        if victim.candidate == other.candidate {
            return true;
        }

        // Check if a bound would previously have been removed when normalizing
        // the param_env so that it can be given the lowest priority. See
        // #50825 for the motivation for this.
        let is_global =
            |cand: &ty::PolyTraitRef<'_>| cand.is_global() && !cand.has_late_bound_regions();

        // (*) Prefer `BuiltinCandidate { has_nested: false }`, `PointeeCandidate`,
        // and `DiscriminantKindCandidate` to anything else.
        //
        // This is a fix for #53123 and prevents winnowing from accidentally extending the
        // lifetime of a variable.
        match (&other.candidate, &victim.candidate) {
            (_, AutoImplCandidate(..)) | (AutoImplCandidate(..), _) => {
                bug!(
                    "default implementations shouldn't be recorded \
                    when there are other valid candidates"
                );
            }

            // (*)
            (
                BuiltinCandidate { has_nested: false }
                | DiscriminantKindCandidate
                | PointeeCandidate,
                _,
            ) => true,
            (
                _,
                BuiltinCandidate { has_nested: false }
                | DiscriminantKindCandidate
                | PointeeCandidate,
            ) => false,

            (ParamCandidate(other), ParamCandidate(victim)) => {
                let value_same_except_bound_vars = other.value.skip_binder()
                    == victim.value.skip_binder()
                    && !other.value.skip_binder().has_escaping_bound_vars();
                if value_same_except_bound_vars {
                    // See issue #84398. In short, we can generate multiple ParamCandidates which are
                    // the same except for unused bound vars. Just pick the one with the fewest bound vars
                    // or the current one if tied (they should both evaluate to the same answer). This is
                    // probably best characterized as a "hack", since we might prefer to just do our
                    // best to *not* create essentially duplicate candidates in the first place.
                    other.value.bound_vars().len() <= victim.value.bound_vars().len()
                } else if other.value == victim.value && victim.constness == Constness::NotConst {
                    // Drop otherwise equivalent non-const candidates in favor of const candidates.
                    true
                } else {
                    false
                }
            }

            // Global bounds from the where clause should be ignored
            // here (see issue #50825). Otherwise, we have a where
            // clause so don't go around looking for impls.
            // Arbitrarily give param candidates priority
            // over projection and object candidates.
            (
                ParamCandidate(ref cand),
                ImplCandidate(..)
                | ClosureCandidate
                | GeneratorCandidate
                | FnPointerCandidate
                | BuiltinObjectCandidate
                | BuiltinUnsizeCandidate
                | BuiltinCandidate { .. }
                | TraitAliasCandidate(..)
                | ObjectCandidate(_)
                | ProjectionCandidate(_),
            ) => !is_global(&cand.value),
            (ObjectCandidate(_) | ProjectionCandidate(_), ParamCandidate(ref cand)) => {
                // Prefer these to a global where-clause bound
                // (see issue #50825).
                is_global(&cand.value)
            }
            (
                ImplCandidate(_)
                | ClosureCandidate
                | GeneratorCandidate
                | FnPointerCandidate
                | BuiltinObjectCandidate
                | BuiltinUnsizeCandidate
                | BuiltinCandidate { has_nested: true }
                | TraitAliasCandidate(..),
                ParamCandidate(ref cand),
            ) => {
                // Prefer these to a global where-clause bound
                // (see issue #50825).
                is_global(&cand.value) && other.evaluation.must_apply_modulo_regions()
            }

            (ProjectionCandidate(i), ProjectionCandidate(j))
            | (ObjectCandidate(i), ObjectCandidate(j)) => {
                // Arbitrarily pick the lower numbered candidate for backwards
                // compatibility reasons. Don't let this affect inference.
                i < j && !needs_infer
            }
            (ObjectCandidate(_), ProjectionCandidate(_))
            | (ProjectionCandidate(_), ObjectCandidate(_)) => {
                bug!("Have both object and projection candidate")
            }

            // Arbitrarily give projection and object candidates priority.
            (
                ObjectCandidate(_) | ProjectionCandidate(_),
                ImplCandidate(..)
                | ClosureCandidate
                | GeneratorCandidate
                | FnPointerCandidate
                | BuiltinObjectCandidate
                | BuiltinUnsizeCandidate
                | BuiltinCandidate { .. }
                | TraitAliasCandidate(..),
            ) => true,

            (
                ImplCandidate(..)
                | ClosureCandidate
                | GeneratorCandidate
                | FnPointerCandidate
                | BuiltinObjectCandidate
                | BuiltinUnsizeCandidate
                | BuiltinCandidate { .. }
                | TraitAliasCandidate(..),
                ObjectCandidate(_) | ProjectionCandidate(_),
            ) => false,

            (&ImplCandidate(other_def), &ImplCandidate(victim_def)) => {
                // See if we can toss out `victim` based on specialization.
                // This requires us to know *for sure* that the `other` impl applies
                // i.e., `EvaluatedToOk`.
                if other.evaluation.must_apply_modulo_regions() {
                    let tcx = self.tcx();
                    if tcx.specializes((other_def, victim_def)) {
                        return true;
                    }
                    return match tcx.impls_are_allowed_to_overlap(other_def, victim_def) {
                        Some(ty::ImplOverlapKind::Permitted { marker: true }) => {
                            // Subtle: If the predicate we are evaluating has inference
                            // variables, do *not* allow discarding candidates due to
                            // marker trait impls.
                            //
                            // Without this restriction, we could end up accidentally
                            // constrainting inference variables based on an arbitrarily
                            // chosen trait impl.
                            //
                            // Imagine we have the following code:
                            //
                            // ```rust
                            // #[marker] trait MyTrait {}
                            // impl MyTrait for u8 {}
                            // impl MyTrait for bool {}
                            // ```
                            //
                            // And we are evaluating the predicate `<_#0t as MyTrait>`.
                            //
                            // During selection, we will end up with one candidate for each
                            // impl of `MyTrait`. If we were to discard one impl in favor
                            // of the other, we would be left with one candidate, causing
                            // us to "successfully" select the predicate, unifying
                            // _#0t with (for example) `u8`.
                            //
                            // However, we have no reason to believe that this unification
                            // is correct - we've essentially just picked an arbitrary
                            // *possibility* for _#0t, and required that this be the *only*
                            // possibility.
                            //
                            // Eventually, we will either:
                            // 1) Unify all inference variables in the predicate through
                            // some other means (e.g. type-checking of a function). We will
                            // then be in a position to drop marker trait candidates
                            // without constraining inference variables (since there are
                            // none left to constrin)
                            // 2) Be left with some unconstrained inference variables. We
                            // will then correctly report an inference error, since the
                            // existence of multiple marker trait impls tells us nothing
                            // about which one should actually apply.
                            !needs_infer
                        }
                        Some(_) => true,
                        None => false,
                    };
                } else {
                    false
                }
            }

            // Everything else is ambiguous
            (
                ImplCandidate(_)
                | ClosureCandidate
                | GeneratorCandidate
                | FnPointerCandidate
                | BuiltinObjectCandidate
                | BuiltinUnsizeCandidate
                | BuiltinCandidate { has_nested: true }
                | TraitAliasCandidate(..),
                ImplCandidate(_)
                | ClosureCandidate
                | GeneratorCandidate
                | FnPointerCandidate
                | BuiltinObjectCandidate
                | BuiltinUnsizeCandidate
                | BuiltinCandidate { has_nested: true }
                | TraitAliasCandidate(..),
            ) => false,
        }
    }

    fn sized_conditions(
        &mut self,
        obligation: &TraitObligation<'tcx>,
    ) -> BuiltinImplConditions<'tcx> {
        use self::BuiltinImplConditions::{Ambiguous, None, Where};

        // NOTE: binder moved to (*)
        let self_ty = self.infcx.shallow_resolve(obligation.predicate.skip_binder().self_ty());

        match self_ty.kind() {
            ty::Infer(ty::IntVar(_) | ty::FloatVar(_))
            | ty::Uint(_)
            | ty::Int(_)
            | ty::Bool
            | ty::Float(_)
            | ty::FnDef(..)
            | ty::FnPtr(_)
            | ty::RawPtr(..)
            | ty::Char
            | ty::Ref(..)
            | ty::Generator(..)
            | ty::GeneratorWitness(..)
            | ty::Array(..)
            | ty::Closure(..)
            | ty::Never
            | ty::Error(_) => {
                // safe for everything
                Where(ty::Binder::dummy(Vec::new()))
            }

            ty::Str | ty::Slice(_) | ty::Dynamic(..) | ty::Foreign(..) => None,

            ty::Tuple(tys) => Where(
                obligation
                    .predicate
                    .rebind(tys.last().into_iter().map(|k| k.expect_ty()).collect()),
            ),

            ty::Adt(def, substs) => {
                let sized_crit = def.sized_constraint(self.tcx());
                // (*) binder moved here
                Where(
                    obligation.predicate.rebind({
                        sized_crit.iter().map(|ty| ty.subst(self.tcx(), substs)).collect()
                    }),
                )
            }

            ty::Projection(_) | ty::Param(_) | ty::Opaque(..) => None,
            ty::Infer(ty::TyVar(_)) => Ambiguous,

            ty::Placeholder(..)
            | ty::Bound(..)
            | ty::Infer(ty::FreshTy(_) | ty::FreshIntTy(_) | ty::FreshFloatTy(_)) => {
                bug!("asked to assemble builtin bounds of unexpected type: {:?}", self_ty);
            }
        }
    }

    fn copy_clone_conditions(
        &mut self,
        obligation: &TraitObligation<'tcx>,
    ) -> BuiltinImplConditions<'tcx> {
        // NOTE: binder moved to (*)
        let self_ty = self.infcx.shallow_resolve(obligation.predicate.skip_binder().self_ty());

        use self::BuiltinImplConditions::{Ambiguous, None, Where};

        match *self_ty.kind() {
            ty::Infer(ty::IntVar(_))
            | ty::Infer(ty::FloatVar(_))
            | ty::FnDef(..)
            | ty::FnPtr(_)
            | ty::Error(_) => Where(ty::Binder::dummy(Vec::new())),

            ty::Uint(_)
            | ty::Int(_)
            | ty::Bool
            | ty::Float(_)
            | ty::Char
            | ty::RawPtr(..)
            | ty::Never
            | ty::Ref(_, _, hir::Mutability::Not) => {
                // Implementations provided in libcore
                None
            }

            ty::Dynamic(..)
            | ty::Str
            | ty::Slice(..)
            | ty::Generator(..)
            | ty::GeneratorWitness(..)
            | ty::Foreign(..)
            | ty::Ref(_, _, hir::Mutability::Mut) => None,

            ty::Array(element_ty, _) => {
                // (*) binder moved here
                Where(obligation.predicate.rebind(vec![element_ty]))
            }

            ty::Tuple(tys) => {
                // (*) binder moved here
                Where(obligation.predicate.rebind(tys.iter().map(|k| k.expect_ty()).collect()))
            }

            ty::Closure(_, substs) => {
                // (*) binder moved here
                let ty = self.infcx.shallow_resolve(substs.as_closure().tupled_upvars_ty());
                if let ty::Infer(ty::TyVar(_)) = ty.kind() {
                    // Not yet resolved.
                    Ambiguous
                } else {
                    Where(obligation.predicate.rebind(substs.as_closure().upvar_tys().collect()))
                }
            }

            ty::Adt(..) | ty::Projection(..) | ty::Param(..) | ty::Opaque(..) => {
                // Fallback to whatever user-defined impls exist in this case.
                None
            }

            ty::Infer(ty::TyVar(_)) => {
                // Unbound type variable. Might or might not have
                // applicable impls and so forth, depending on what
                // those type variables wind up being bound to.
                Ambiguous
            }

            ty::Placeholder(..)
            | ty::Bound(..)
            | ty::Infer(ty::FreshTy(_) | ty::FreshIntTy(_) | ty::FreshFloatTy(_)) => {
                bug!("asked to assemble builtin bounds of unexpected type: {:?}", self_ty);
            }
        }
    }

    /// For default impls, we need to break apart a type into its
    /// "constituent types" -- meaning, the types that it contains.
    ///
    /// Here are some (simple) examples:
    ///
    /// ```
    /// (i32, u32) -> [i32, u32]
    /// Foo where struct Foo { x: i32, y: u32 } -> [i32, u32]
    /// Bar<i32> where struct Bar<T> { x: T, y: u32 } -> [i32, u32]
    /// Zed<i32> where enum Zed { A(T), B(u32) } -> [i32, u32]
    /// ```
    fn constituent_types_for_ty(
        &self,
        t: ty::Binder<'tcx, Ty<'tcx>>,
    ) -> ty::Binder<'tcx, Vec<Ty<'tcx>>> {
        match *t.skip_binder().kind() {
            ty::Uint(_)
            | ty::Int(_)
            | ty::Bool
            | ty::Float(_)
            | ty::FnDef(..)
            | ty::FnPtr(_)
            | ty::Str
            | ty::Error(_)
            | ty::Infer(ty::IntVar(_) | ty::FloatVar(_))
            | ty::Never
            | ty::Char => ty::Binder::dummy(Vec::new()),

            ty::Placeholder(..)
            | ty::Dynamic(..)
            | ty::Param(..)
            | ty::Foreign(..)
            | ty::Projection(..)
            | ty::Bound(..)
            | ty::Infer(ty::TyVar(_) | ty::FreshTy(_) | ty::FreshIntTy(_) | ty::FreshFloatTy(_)) => {
                bug!("asked to assemble constituent types of unexpected type: {:?}", t);
            }

            ty::RawPtr(ty::TypeAndMut { ty: element_ty, .. }) | ty::Ref(_, element_ty, _) => {
                t.rebind(vec![element_ty])
            }

            ty::Array(element_ty, _) | ty::Slice(element_ty) => t.rebind(vec![element_ty]),

            ty::Tuple(ref tys) => {
                // (T1, ..., Tn) -- meets any bound that all of T1...Tn meet
                t.rebind(tys.iter().map(|k| k.expect_ty()).collect())
            }

            ty::Closure(_, ref substs) => {
                let ty = self.infcx.shallow_resolve(substs.as_closure().tupled_upvars_ty());
                t.rebind(vec![ty])
            }

            ty::Generator(_, ref substs, _) => {
                let ty = self.infcx.shallow_resolve(substs.as_generator().tupled_upvars_ty());
                let witness = substs.as_generator().witness();
                t.rebind(vec![ty].into_iter().chain(iter::once(witness)).collect())
            }

            ty::GeneratorWitness(types) => {
                debug_assert!(!types.has_escaping_bound_vars());
                types.map_bound(|types| types.to_vec())
            }

            // For `PhantomData<T>`, we pass `T`.
            ty::Adt(def, substs) if def.is_phantom_data() => t.rebind(substs.types().collect()),

            ty::Adt(def, substs) => {
                t.rebind(def.all_fields().map(|f| f.ty(self.tcx(), substs)).collect())
            }

            ty::Opaque(def_id, substs) => {
                // We can resolve the `impl Trait` to its concrete type,
                // which enforces a DAG between the functions requiring
                // the auto trait bounds in question.
                t.rebind(vec![self.tcx().type_of(def_id).subst(self.tcx(), substs)])
            }
        }
    }

    fn collect_predicates_for_types(
        &mut self,
        param_env: ty::ParamEnv<'tcx>,
        cause: ObligationCause<'tcx>,
        recursion_depth: usize,
        trait_def_id: DefId,
        types: ty::Binder<'tcx, Vec<Ty<'tcx>>>,
    ) -> Vec<PredicateObligation<'tcx>> {
        // Because the types were potentially derived from
        // higher-ranked obligations they may reference late-bound
        // regions. For example, `for<'a> Foo<&'a i32> : Copy` would
        // yield a type like `for<'a> &'a i32`. In general, we
        // maintain the invariant that we never manipulate bound
        // regions, so we have to process these bound regions somehow.
        //
        // The strategy is to:
        //
        // 1. Instantiate those regions to placeholder regions (e.g.,
        //    `for<'a> &'a i32` becomes `&0 i32`.
        // 2. Produce something like `&'0 i32 : Copy`
        // 3. Re-bind the regions back to `for<'a> &'a i32 : Copy`

        types
            .as_ref()
            .skip_binder() // binder moved -\
            .iter()
            .flat_map(|ty| {
                let ty: ty::Binder<'tcx, Ty<'tcx>> = types.rebind(ty); // <----/

                self.infcx.commit_unconditionally(|_| {
                    let placeholder_ty = self.infcx.replace_bound_vars_with_placeholders(ty);
                    let Normalized { value: normalized_ty, mut obligations } =
                        ensure_sufficient_stack(|| {
                            project::normalize_with_depth(
                                self,
                                param_env,
                                cause.clone(),
                                recursion_depth,
                                placeholder_ty,
                            )
                        });
                    let placeholder_obligation = predicate_for_trait_def(
                        self.tcx(),
                        param_env,
                        cause.clone(),
                        trait_def_id,
                        recursion_depth,
                        normalized_ty,
                        &[],
                    );
                    obligations.push(placeholder_obligation);
                    obligations
                })
            })
            .collect()
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

    fn rematch_impl(
        &mut self,
        impl_def_id: DefId,
        obligation: &TraitObligation<'tcx>,
    ) -> Normalized<'tcx, SubstsRef<'tcx>> {
        match self.match_impl(impl_def_id, obligation) {
            Ok(substs) => substs,
            Err(()) => {
                bug!(
                    "Impl {:?} was matchable against {:?} but now is not",
                    impl_def_id,
                    obligation
                );
            }
        }
    }

    fn match_impl(
        &mut self,
        impl_def_id: DefId,
        obligation: &TraitObligation<'tcx>,
    ) -> Result<Normalized<'tcx, SubstsRef<'tcx>>, ()> {
        debug!(?impl_def_id, ?obligation, "match_impl");
        let impl_trait_ref = self.tcx().impl_trait_ref(impl_def_id).unwrap();

        // Before we create the substitutions and everything, first
        // consider a "quick reject". This avoids creating more types
        // and so forth that we need to.
        if self.fast_reject_trait_refs(obligation, &impl_trait_ref) {
            return Err(());
        }

        let placeholder_obligation =
            self.infcx().replace_bound_vars_with_placeholders(obligation.predicate);
        let placeholder_obligation_trait_ref = placeholder_obligation.trait_ref;

        let impl_substs = self.infcx.fresh_substs_for_item(obligation.cause.span, impl_def_id);

        let impl_trait_ref = impl_trait_ref.subst(self.tcx(), impl_substs);

        let Normalized { value: impl_trait_ref, obligations: mut nested_obligations } =
            ensure_sufficient_stack(|| {
                project::normalize_with_depth(
                    self,
                    obligation.param_env,
                    obligation.cause.clone(),
                    obligation.recursion_depth + 1,
                    impl_trait_ref,
                )
            });

        debug!(?impl_trait_ref, ?placeholder_obligation_trait_ref);

        let InferOk { obligations, .. } = self
            .infcx
            .at(&obligation.cause, obligation.param_env)
            .eq(placeholder_obligation_trait_ref, impl_trait_ref)
            .map_err(|e| debug!("match_impl: failed eq_trait_refs due to `{}`", e))?;
        nested_obligations.extend(obligations);

        if !self.intercrate
            && self.tcx().impl_polarity(impl_def_id) == ty::ImplPolarity::Reservation
        {
            debug!("match_impl: reservation impls only apply in intercrate mode");
            return Err(());
        }

        debug!(?impl_substs, "match_impl: success");
        Ok(Normalized { value: impl_substs, obligations: nested_obligations })
    }

    fn fast_reject_trait_refs(
        &mut self,
        obligation: &TraitObligation<'_>,
        impl_trait_ref: &ty::TraitRef<'_>,
    ) -> bool {
        // We can avoid creating type variables and doing the full
        // substitution if we find that any of the input types, when
        // simplified, do not match.

        iter::zip(obligation.predicate.skip_binder().trait_ref.substs, impl_trait_ref.substs).any(
            |(obligation_arg, impl_arg)| {
                match (obligation_arg.unpack(), impl_arg.unpack()) {
                    (GenericArgKind::Type(obligation_ty), GenericArgKind::Type(impl_ty)) => {
                        let simplified_obligation_ty =
                            fast_reject::simplify_type(self.tcx(), obligation_ty, true);
                        let simplified_impl_ty =
                            fast_reject::simplify_type(self.tcx(), impl_ty, false);

                        simplified_obligation_ty.is_some()
                            && simplified_impl_ty.is_some()
                            && simplified_obligation_ty != simplified_impl_ty
                    }
                    (GenericArgKind::Lifetime(_), GenericArgKind::Lifetime(_)) => {
                        // Lifetimes can never cause a rejection.
                        false
                    }
                    (GenericArgKind::Const(_), GenericArgKind::Const(_)) => {
                        // Conservatively ignore consts (i.e. assume they might
                        // unify later) until we have `fast_reject` support for
                        // them (if we'll ever need it, even).
                        false
                    }
                    _ => unreachable!(),
                }
            },
        )
    }

    /// Normalize `where_clause_trait_ref` and try to match it against
    /// `obligation`. If successful, return any predicates that
    /// result from the normalization.
    fn match_where_clause_trait_ref(
        &mut self,
        obligation: &TraitObligation<'tcx>,
        where_clause_trait_ref: ty::PolyTraitRef<'tcx>,
    ) -> Result<Vec<PredicateObligation<'tcx>>, ()> {
        self.match_poly_trait_ref(obligation, where_clause_trait_ref)
    }

    /// Returns `Ok` if `poly_trait_ref` being true implies that the
    /// obligation is satisfied.
    fn match_poly_trait_ref(
        &mut self,
        obligation: &TraitObligation<'tcx>,
        poly_trait_ref: ty::PolyTraitRef<'tcx>,
    ) -> Result<Vec<PredicateObligation<'tcx>>, ()> {
        debug!(?obligation, ?poly_trait_ref, "match_poly_trait_ref");

        self.infcx
            .at(&obligation.cause, obligation.param_env)
            .sup(obligation.predicate.to_poly_trait_ref(), poly_trait_ref)
            .map(|InferOk { obligations, .. }| obligations)
            .map_err(|_| ())
    }

    ///////////////////////////////////////////////////////////////////////////
    // Miscellany

    fn match_fresh_trait_refs(
        &self,
        previous: ty::PolyTraitRef<'tcx>,
        current: ty::PolyTraitRef<'tcx>,
        param_env: ty::ParamEnv<'tcx>,
    ) -> bool {
        let mut matcher = ty::_match::Match::new(self.tcx(), param_env);
        matcher.relate(previous, current).is_ok()
    }

    fn push_stack<'o>(
        &mut self,
        previous_stack: TraitObligationStackList<'o, 'tcx>,
        obligation: &'o TraitObligation<'tcx>,
    ) -> TraitObligationStack<'o, 'tcx> {
        let fresh_trait_ref =
            obligation.predicate.to_poly_trait_ref().fold_with(&mut self.freshener);

        let dfn = previous_stack.cache().next_dfn();
        let depth = previous_stack.depth() + 1;
        TraitObligationStack {
            obligation,
            fresh_trait_ref,
            reached_depth: Cell::new(depth),
            previous: previous_stack,
            dfn,
            depth,
        }
    }

    fn closure_trait_ref_unnormalized(
        &mut self,
        obligation: &TraitObligation<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> ty::PolyTraitRef<'tcx> {
        debug!(?obligation, ?substs, "closure_trait_ref_unnormalized");
        let closure_sig = substs.as_closure().sig();

        debug!(?closure_sig);

        // (1) Feels icky to skip the binder here, but OTOH we know
        // that the self-type is an unboxed closure type and hence is
        // in fact unparameterized (or at least does not reference any
        // regions bound in the obligation). Still probably some
        // refactoring could make this nicer.
        closure_trait_ref_and_return_type(
            self.tcx(),
            obligation.predicate.def_id(),
            obligation.predicate.skip_binder().self_ty(), // (1)
            closure_sig,
            util::TupleArgumentsFlag::No,
        )
        .map_bound(|(trait_ref, _)| trait_ref)
    }

    fn generator_trait_ref_unnormalized(
        &mut self,
        obligation: &TraitObligation<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> ty::PolyTraitRef<'tcx> {
        let gen_sig = substs.as_generator().poly_sig();

        // (1) Feels icky to skip the binder here, but OTOH we know
        // that the self-type is an generator type and hence is
        // in fact unparameterized (or at least does not reference any
        // regions bound in the obligation). Still probably some
        // refactoring could make this nicer.

        super::util::generator_trait_ref_and_outputs(
            self.tcx(),
            obligation.predicate.def_id(),
            obligation.predicate.skip_binder().self_ty(), // (1)
            gen_sig,
        )
        .map_bound(|(trait_ref, ..)| trait_ref)
    }

    /// Returns the obligations that are implied by instantiating an
    /// impl or trait. The obligations are substituted and fully
    /// normalized. This is used when confirming an impl or default
    /// impl.
    fn impl_or_trait_obligations(
        &mut self,
        cause: ObligationCause<'tcx>,
        recursion_depth: usize,
        param_env: ty::ParamEnv<'tcx>,
        def_id: DefId,           // of impl or trait
        substs: SubstsRef<'tcx>, // for impl or trait
    ) -> Vec<PredicateObligation<'tcx>> {
        debug!(?def_id, "impl_or_trait_obligations");
        let tcx = self.tcx();

        // To allow for one-pass evaluation of the nested obligation,
        // each predicate must be preceded by the obligations required
        // to normalize it.
        // for example, if we have:
        //    impl<U: Iterator<Item: Copy>, V: Iterator<Item = U>> Foo for V
        // the impl will have the following predicates:
        //    <V as Iterator>::Item = U,
        //    U: Iterator, U: Sized,
        //    V: Iterator, V: Sized,
        //    <U as Iterator>::Item: Copy
        // When we substitute, say, `V => IntoIter<u32>, U => $0`, the last
        // obligation will normalize to `<$0 as Iterator>::Item = $1` and
        // `$1: Copy`, so we must ensure the obligations are emitted in
        // that order.
        let predicates = tcx.predicates_of(def_id);
        assert_eq!(predicates.parent, None);
        let mut obligations = Vec::with_capacity(predicates.predicates.len());
        for (predicate, _) in predicates.predicates {
            let predicate = normalize_with_depth_to(
                self,
                param_env,
                cause.clone(),
                recursion_depth,
                predicate.subst(tcx, substs),
                &mut obligations,
            );
            obligations.push(Obligation {
                cause: cause.clone(),
                recursion_depth,
                param_env,
                predicate,
            });
        }

        // We are performing deduplication here to avoid exponential blowups
        // (#38528) from happening, but the real cause of the duplication is
        // unknown. What we know is that the deduplication avoids exponential
        // amount of predicates being propagated when processing deeply nested
        // types.
        //
        // This code is hot enough that it's worth avoiding the allocation
        // required for the FxHashSet when possible. Special-casing lengths 0,
        // 1 and 2 covers roughly 75-80% of the cases.
        if obligations.len() <= 1 {
            // No possibility of duplicates.
        } else if obligations.len() == 2 {
            // Only two elements. Drop the second if they are equal.
            if obligations[0] == obligations[1] {
                obligations.truncate(1);
            }
        } else {
            // Three or more elements. Use a general deduplication process.
            let mut seen = FxHashSet::default();
            obligations.retain(|i| seen.insert(i.clone()));
        }

        obligations
    }
}

trait TraitObligationExt<'tcx> {
    fn derived_cause(
        &self,
        variant: fn(DerivedObligationCause<'tcx>) -> ObligationCauseCode<'tcx>,
    ) -> ObligationCause<'tcx>;
}

impl<'tcx> TraitObligationExt<'tcx> for TraitObligation<'tcx> {
    fn derived_cause(
        &self,
        variant: fn(DerivedObligationCause<'tcx>) -> ObligationCauseCode<'tcx>,
    ) -> ObligationCause<'tcx> {
        /*!
         * Creates a cause for obligations that are derived from
         * `obligation` by a recursive search (e.g., for a builtin
         * bound, or eventually a `auto trait Foo`). If `obligation`
         * is itself a derived obligation, this is just a clone, but
         * otherwise we create a "derived obligation" cause so as to
         * keep track of the original root obligation for error
         * reporting.
         */

        let obligation = self;

        // NOTE(flaper87): As of now, it keeps track of the whole error
        // chain. Ideally, we should have a way to configure this either
        // by using -Z verbose or just a CLI argument.
        let derived_cause = DerivedObligationCause {
            parent_trait_ref: obligation.predicate.to_poly_trait_ref(),
            parent_code: Rc::new(obligation.cause.code.clone()),
        };
        let derived_code = variant(derived_cause);
        ObligationCause::new(obligation.cause.span, obligation.cause.body_id, derived_code)
    }
}
