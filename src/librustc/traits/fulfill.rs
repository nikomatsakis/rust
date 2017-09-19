// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use infer::InferCtxt;
use ty::{self, Ty, TypeFoldable, ToPredicate};
use ty::error::ExpectedFound;
use rustc_data_structures::obligation_forest::{ObligationForest, Error};
use rustc_data_structures::obligation_forest::{ForestObligation, ObligationProcessor};
use std::marker::PhantomData;
use syntax::ast;
use util::nodemap::NodeMap;
use hir::def_id::DefId;

use super::CodeAmbiguity;
use super::CodeProjectionError;
use super::CodeSelectionError;
use super::{FulfillmentError, FulfillmentErrorCode};
use super::{ObligationCause, PredicateAtomObligation, PredicateObligation, Obligation};
use super::project;
use super::select::SelectionContext;
use super::{Unimplemented, ConstEvalFailure};

impl<'tcx> ForestObligation for PendingPredicateAtomObligation<'tcx> {
    type Predicate = ty::PredicateAtom<'tcx>;

    fn as_predicate(&self) -> &Self::Predicate { &self.obligation.predicate }
}

/// The fulfillment context is used to drive trait resolution.  It
/// consists of a list of obligations that must be (eventually)
/// satisfied. The job is to track which are satisfied, which yielded
/// errors, and which are still pending. At any point, users can call
/// `select_where_possible`, and the fulfillment context will try to do
/// selection, retaining only those obligations that remain
/// ambiguous. This may be helpful in pushing type inference
/// along. Once all type inference constraints have been generated, the
/// method `select_all_or_error` can be used to report any remaining
/// ambiguous cases as errors.

pub struct FulfillmentContext<'tcx> {
    // A list of all obligations that have been registered with this
    // fulfillment context.
    predicates: ObligationForest<PendingPredicateAtomObligation<'tcx>>,

    // A set of predicates that are useful for inferring closure signatures.
    //
    // We are looking to help out with a scenario like this:
    //
    // ```
    // foo(|x| use(*x))
    //
    // fn foo<T>(t: T) where T: FnMut(&u32) { .. }
    // ```
    //
    // In this case, in the expression `foo(|x| use(*x))`, the type
    // variable `T` is first instantiated with an inference variable
    // `?T` (as part of the subexpression `foo`) and the obligation
    // that `?T: FnMut(&u32)` is registered; actually, a few
    // obligations get registered, but the most helpful thing is a
    // projection predicate `for<'a> <?T as FnMut<(&'a u32,)>>::Output
    // = ()`. We then typecheck the arguments. The closure expression
    // `|x|` gets that its expected type is `?T`, but that does not
    // tell it anything about its expected signature.  To solve this,
    // it needs to trawl through the list of pending prediates. That's
    // where this vector comes in.
    //
    // This vector stores a copy of predicate that gets registered where the
    // following conditions are met:
    //
    // 0. The predicate is in universe 0.
    // 1. The self-type is an uninstantiated type variable.
    // 2. It is a projection or trait-ref of a closure trait.
    //
    // We periodically prune out cases where the self-type got
    // instantiated, as they are no longer of potential use.
    //
    // Closures can read the current state via the
    // `pending_closure_predicates()` accessor.
    pending_closure_predicates: Vec<ty::Predicate<'tcx>>,

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

#[derive(Clone)]
pub struct RegionObligation<'tcx> {
    pub param_env: ty::ParamEnv<'tcx>,
    pub sub_region: ty::Region<'tcx>,
    pub sup_type: Ty<'tcx>,
    pub cause: ObligationCause<'tcx>,
}

#[derive(Clone, Debug)]
pub struct PendingPredicateAtomObligation<'tcx> {
    pub obligation: PredicateAtomObligation<'tcx>,
    pub stalled_on: Vec<Ty<'tcx>>,
}

impl<'a, 'gcx, 'tcx> FulfillmentContext<'tcx> {
    /// Creates a new fulfillment context.
    pub fn new() -> FulfillmentContext<'tcx> {
        FulfillmentContext {
            predicates: ObligationForest::new(),
            region_obligations: NodeMap(),
            pending_closure_predicates: vec![],
        }
    }

    /// "Normalize" a projection type `<SomeType as SomeTrait>::X` by
    /// creating a fresh type variable `$0` as well as a projection
    /// predicate `<SomeType as SomeTrait>::X == $0`. When the
    /// inference engine runs, it will attempt to find an impl of
    /// `SomeTrait` or a where clause that lets us unify `$0` with
    /// something concrete. If this fails, we'll unify `$0` with
    /// `projection_ty` again.
    pub fn normalize_projection_type(&mut self,
                                     infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                                     param_env: ty::ParamEnv<'tcx>,
                                     projection_ty: ty::ProjectionTy<'tcx>,
                                     cause: ObligationCause<'tcx>)
                                     -> Ty<'tcx>
    {
        debug!("normalize_projection_type(projection_ty={:?})",
               projection_ty);

        assert!(!projection_ty.has_escaping_regions());

        // FIXME(#20304) -- cache

        let mut selcx = SelectionContext::new(infcx);
        let normalized = project::normalize_projection_type(&mut selcx,
                                                            param_env,
                                                            projection_ty,
                                                            cause,
                                                            0);

        for obligation in normalized.obligations {
            self.register_predicate_obligation(infcx, obligation);
        }

        debug!("normalize_projection_type: result={:?}", normalized.value);

        normalized.value
    }

    /// Requires that `ty` must implement the trait with `def_id` in
    /// the given environment. This trait must not have any type
    /// parameters (except for `Self`).
    pub fn register_bound(&mut self,
                          infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                          param_env: ty::ParamEnv<'tcx>,
                          ty: Ty<'tcx>,
                          def_id: DefId,
                          cause: ObligationCause<'tcx>)
    {
        let trait_ref = ty::TraitRef {
            def_id,
            substs: infcx.tcx.mk_substs_trait(ty, &[]),
        };
        self.register_predicate_obligation(infcx, Obligation {
            cause,
            recursion_depth: 0,
            param_env,
            predicate: trait_ref.to_predicate()
        });
    }

    pub fn register_region_obligation(&mut self,
                                      param_env: ty::ParamEnv<'tcx>,
                                      t_a: Ty<'tcx>,
                                      r_b: ty::Region<'tcx>,
                                      cause: ObligationCause<'tcx>)
    {
        register_region_obligation(param_env, t_a, r_b, cause, &mut self.region_obligations);
    }

    pub fn register_predicate_obligation(&mut self,
                                         infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                                         obligation: PredicateObligation<'tcx>)
    {
        // Important: record closure predicates *before* we skolemize!
        // Otherwise it is too late to recover binding information.
        self.record_closure_predicate_if_relevant(infcx, &obligation);

        let atom_obligation = infcx.skolemize_predicate_obligation(&obligation);
        self.register_predicate_atom_obligation(infcx, atom_obligation);
    }

    fn register_predicate_atom_obligation(&mut self,
                                          infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                                          obligation: PredicateAtomObligation<'tcx>)
    {
        // this helps to reduce duplicate errors, as well as making
        // debug output much nicer to read and so on.
        let obligation = infcx.resolve_type_vars_if_possible(&obligation);

        debug!("register_predicate_atom_obligation(obligation={:?})", obligation);

        assert!(!infcx.is_in_snapshot());

        self.predicates.register_obligation(PendingPredicateAtomObligation {
            obligation,
            stalled_on: vec![]
        });
    }

    fn record_closure_predicate_if_relevant(&mut self,
                                            infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                                            obligation: &PredicateObligation<'tcx>) {
        if obligation.param_env.universe != ty::UniverseIndex::ROOT {
            return;
        }

        if Self::is_closure_predicate(infcx, &obligation.predicate) {
            // Don't let the vector keep growing without bound: clear
            // out anything that is no longer relevant.
            self.pending_closure_predicates.retain(|p| Self::is_closure_predicate(infcx, p));
            self.pending_closure_predicates.push(obligation.predicate);
        }
    }

    fn is_closure_predicate(infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                            predicate: &ty::Predicate<'tcx>)
                            -> bool
    {
        // OK to skip binder. We are just looking for a (free) type
        // variable.
        let self_ty = match predicate.skip_binders() {
            ty::PredicateAtom::Trait(trait_ref) => trait_ref.self_ty(),
            ty::PredicateAtom::Projection(proj) => proj.to_trait_ref(infcx.tcx).self_ty(),
            _ => return false,
        };

        // Not a type variable? Then not a closure predicate.
        if !self_ty.is_ty_var() {
            return false;
        }

        // If it is a type variable, check if it has been resolved
        // already.  If so, no longer of interest.
        let self_ty = infcx.shallow_resolve(self_ty);
        self_ty.is_ty_var()
    }

    pub fn register_predicate_obligations(&mut self,
                                          infcx: &InferCtxt<'a, 'gcx, 'tcx>,
                                          obligations: Vec<PredicateObligation<'tcx>>)
    {
        for obligation in obligations {
            self.register_predicate_obligation(infcx, obligation);
        }
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

    pub fn select_all_or_error(&mut self,
                               infcx: &InferCtxt<'a, 'gcx, 'tcx>)
                               -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        self.select_where_possible(infcx)?;

        let errors: Vec<_> =
            self.predicates.to_errors(CodeAmbiguity)
                           .into_iter()
                           .map(|e| to_fulfillment_error(e))
                           .collect();
        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    pub fn select_where_possible(&mut self,
                                 infcx: &InferCtxt<'a, 'gcx, 'tcx>)
                                 -> Result<(),Vec<FulfillmentError<'tcx>>>
    {
        let mut selcx = SelectionContext::new(infcx);
        self.select(&mut selcx)
    }

    /// Returns the list of closure obligations that we have seen
    /// which are yet pending (meaning that their self type has not
    /// yet been seen to be resolved to a specific closure type, and
    /// hence they may still be of use).
    ///
    /// See the comment on the field `pending_closure_predicates` for
    /// more information.
    pub fn pending_closure_predicates(&self) -> &[ty::Predicate<'tcx>] {
        &self.pending_closure_predicates
    }

    /// Attempts to select obligations using `selcx`. If `only_new_obligations` is true, then it
    /// only attempts to select obligations that haven't been seen before.
    fn select(&mut self, selcx: &mut SelectionContext<'a, 'gcx, 'tcx>)
              -> Result<(),Vec<FulfillmentError<'tcx>>> {
        debug!("select(obligation-forest-size={})", self.predicates.len());

        let mut errors = Vec::new();

        loop {
            debug!("select: starting another iteration");

            // Process pending obligations.
            let outcome = self.predicates.process_obligations(&mut FulfillProcessor {
                selcx,
                region_obligations: &mut self.region_obligations,
            });
            debug!("select: outcome={:?}", outcome);

            // FIXME: if we kept the original cache key, we could mark projection
            // obligations as complete for the projection cache here.

            errors.extend(
                outcome.errors.into_iter()
                              .map(|e| to_fulfillment_error(e)));

            // If nothing new was added, no need to keep looping.
            if outcome.stalled {
                break;
            }
        }

        debug!("select({} predicates remaining, {} errors) done",
               self.predicates.len(), errors.len());

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }
}

struct FulfillProcessor<'a, 'b: 'a, 'gcx: 'tcx, 'tcx: 'b> {
    selcx: &'a mut SelectionContext<'b, 'gcx, 'tcx>,
    region_obligations: &'a mut NodeMap<Vec<RegionObligation<'tcx>>>,
}

impl<'a, 'b, 'gcx, 'tcx> ObligationProcessor for FulfillProcessor<'a, 'b, 'gcx, 'tcx> {
    type Obligation = PendingPredicateAtomObligation<'tcx>;
    type Error = FulfillmentErrorCode<'tcx>;

    fn process_obligation(&mut self,
                          obligation: &mut Self::Obligation)
                          -> Result<Option<Vec<Self::Obligation>>, Self::Error>
    {
        let opt_obligations = process_predicate(self.selcx, obligation, self.region_obligations)?;

        // Return Ok(None) if we failed to make any progress.
        let obligations = match opt_obligations {
            None => return Ok(None),
            Some(vec) => vec,
        };

        // To start, we have to fully skolemize all the
        // subobligations, removing any higher-ranked bindings.
        let atom_obligations = obligations.iter().map(|obligation| {
            self.selcx.infcx().skolemize_predicate_obligation(obligation)
        });

        // Next, convert them into "pending obligations" that are not yet stalled on anything.
        let pending_obligations = atom_obligations.map(|atom_obligation| {
            PendingPredicateAtomObligation {
                obligation: atom_obligation,
                stalled_on: vec![],
            }
        });

        Ok(Some(pending_obligations.collect()))
    }

    fn process_backedge<'c, I>(&mut self, cycle: I,
                               _marker: PhantomData<&'c PendingPredicateAtomObligation<'tcx>>)
        where I: Clone + Iterator<Item=&'c PendingPredicateAtomObligation<'tcx>>,
    {
        if self.selcx.coinductive_match(cycle.clone().map(|s| s.obligation.predicate)) {
            debug!("process_child_obligations: coinductive match");
        } else {
            let cycle : Vec<_> = cycle.map(|c| c.obligation.clone()).collect();
            self.selcx.infcx().report_overflow_error_cycle(&cycle);
        }
    }
}

/// Return the set of type variables contained in a trait ref
fn trait_ref_type_vars<'a, 'gcx, 'tcx>(selcx: &mut SelectionContext<'a, 'gcx, 'tcx>,
                                       t: ty::TraitRef<'tcx>) -> Vec<Ty<'tcx>>
{
    t.input_types()
     .map(|t| selcx.infcx().resolve_type_vars_if_possible(&t))
     .filter(|t| t.has_infer_types())
     .flat_map(|t| t.walk())
     .filter(|t| match t.sty { ty::TyInfer(_) => true, _ => false })
     .collect()
}

/// Processes a predicate obligation and returns either:
/// - `Ok(Some(v))` if the predicate is true, presuming that `v` are also true
/// - `Ok(None)` if we don't have enough info to be sure
/// - `Err` if the predicate does not hold
fn process_predicate<'a, 'gcx, 'tcx>(
    selcx: &mut SelectionContext<'a, 'gcx, 'tcx>,
    pending_obligation: &mut PendingPredicateAtomObligation<'tcx>,
    region_obligations: &mut NodeMap<Vec<RegionObligation<'tcx>>>)
    -> Result<Option<Vec<PredicateObligation<'tcx>>>,
              FulfillmentErrorCode<'tcx>>
{
    // if we were stalled on some unresolved variables, first check
    // whether any of them have been resolved; if not, don't bother
    // doing more work yet
    if !pending_obligation.stalled_on.is_empty() {
        if pending_obligation.stalled_on.iter().all(|&ty| {
            let resolved_ty = selcx.infcx().shallow_resolve(&ty);
            resolved_ty == ty // nothing changed here
        }) {
            debug!("process_predicate: pending obligation {:?} still stalled on {:?}",
                   selcx.infcx().resolve_type_vars_if_possible(&pending_obligation.obligation),
                   pending_obligation.stalled_on);
            return Ok(None);
        }
        pending_obligation.stalled_on = vec![];
    }

    let obligation = &mut pending_obligation.obligation;

    if obligation.predicate.has_infer_types() {
        obligation.predicate = selcx.infcx().resolve_type_vars_if_possible(&obligation.predicate);
    }

    match obligation.predicate {
        ty::PredicateAtom::Trait(trait_ref) => {
            let trait_obligation = obligation.with(trait_ref);

            if trait_ref.is_global() {
                // no type variables present, can use evaluation for better caching.
                // FIXME: consider caching errors too.
                if
                    // make defaulted unit go through the slow path for better warnings,
                    // please remove this when the warnings are removed.
                    !trait_obligation.predicate.self_ty().is_defaulted_unit() &&
                    selcx.evaluate_obligation_conservatively(&obligation)
                {
                    debug!("selecting trait `{:?}` at depth {} evaluated to holds",
                           trait_ref, obligation.recursion_depth);
                    return Ok(Some(vec![]))
                }
            }

            match selcx.select(&trait_obligation) {
                Ok(Some(vtable)) => {
                    debug!("selecting trait `{:?}` at depth {} yielded Ok(Some)",
                           trait_ref, obligation.recursion_depth);
                    Ok(Some(vtable.into_nested_obligations()))
                }
                Ok(None) => {
                    debug!("selecting trait `{:?}` at depth {} yielded Ok(None)",
                           trait_ref, obligation.recursion_depth);

                    // This is a bit subtle: for the most part, the
                    // only reason we can fail to make progress on
                    // trait selection is because we don't have enough
                    // information about the types in the trait. One
                    // exception is that we sometimes haven't decided
                    // what kind of closure a closure is. *But*, in
                    // that case, it turns out, the type of the
                    // closure will also change, because the closure
                    // also includes references to its upvars as part
                    // of its type, and those types are resolved at
                    // the same time.
                    //
                    // FIXME(#32286) logic seems false if no upvars
                    pending_obligation.stalled_on = trait_ref_type_vars(selcx, trait_ref);

                    debug!("process_predicate: pending obligation {:?} now stalled on {:?}",
                           selcx.infcx().resolve_type_vars_if_possible(obligation),
                           pending_obligation.stalled_on);

                    Ok(None)
                }
                Err(selection_err) => {
                    info!("selecting trait `{:?}` at depth {} yielded Err",
                          trait_ref, obligation.recursion_depth);

                    Err(CodeSelectionError(selection_err))
                }
            }
        }

        ty::PredicateAtom::RegionOutlives(data) => {
            match selcx.infcx().region_outlives_predicate(&obligation.cause,
                                                          obligation.param_env,
                                                          data) {
                Ok(()) => Ok(Some(Vec::new())),
                Err(_) => Err(CodeSelectionError(Unimplemented)),
            }
        }

        ty::PredicateAtom::TypeOutlives(ty::OutlivesPredicate(t_a, r_b)) => {
            register_region_obligation(obligation.param_env,
                                       t_a,
                                       r_b,
                                       obligation.cause.clone(),
                                       region_obligations);
            Ok(Some(vec![]))
        }

        ty::PredicateAtom::Projection(data) => {
            let project_obligation = obligation.with(data);
            match project::project_and_unify_type(selcx, &project_obligation) {
                Ok(None) => {
                    let tcx = selcx.tcx();
                    pending_obligation.stalled_on =
                        trait_ref_type_vars(selcx, data.to_trait_ref(tcx));
                    Ok(None)
                }
                Ok(v) => Ok(v),
                Err(e) => Err(CodeProjectionError(e))
            }
        }

        ty::PredicateAtom::ObjectSafe(trait_def_id) => {
            if !selcx.tcx().is_object_safe(trait_def_id) {
                Err(CodeSelectionError(Unimplemented))
            } else {
                Ok(Some(Vec::new()))
            }
        }

        ty::PredicateAtom::ClosureKind(closure_def_id, kind) => {
            match selcx.infcx().closure_kind(closure_def_id) {
                Some(closure_kind) => {
                    if closure_kind.extends(kind) {
                        Ok(Some(vec![]))
                    } else {
                        Err(CodeSelectionError(Unimplemented))
                    }
                }
                None => {
                    Ok(None)
                }
            }
        }

        ty::PredicateAtom::WellFormed(ty) => {
            match ty::wf::obligations(selcx.infcx(),
                                      obligation.param_env,
                                      obligation.cause.body_id,
                                      ty,
                                      obligation.cause.span) {
                None => {
                    pending_obligation.stalled_on = vec![ty];
                    Ok(None)
                }
                s => Ok(s)
            }
        }

        ty::PredicateAtom::Subtype(subtype) => {
            match selcx.infcx().subtype_predicate(&obligation.cause,
                                                  obligation.param_env,
                                                  subtype) {
                None => {
                    // none means that both are unresolved
                    pending_obligation.stalled_on = vec![subtype.a, subtype.b];
                    Ok(None)
                }
                Some(Ok(ok)) => {
                    Ok(Some(ok.obligations))
                }
                Some(Err(err)) => {
                    let expected_found = ExpectedFound::new(subtype.a_is_expected,
                                                            subtype.a,
                                                            subtype.b);
                    Err(FulfillmentErrorCode::CodeSubtypeError(expected_found, err))
                }
            }
        }

        ty::PredicateAtom::ConstEvaluatable(def_id, substs) => {
            match selcx.tcx().lift_to_global(&obligation.param_env) {
                None => {
                    Ok(None)
                }
                Some(param_env) => {
                    match selcx.tcx().lift_to_global(&substs) {
                        None => {
                            pending_obligation.stalled_on = substs.types().collect();
                            Ok(None)
                        }
                        Some(substs) => {
                            match selcx.tcx().at(obligation.cause.span)
                                             .const_eval(param_env.and((def_id, substs))) {
                                Ok(_) => Ok(Some(vec![])),
                                Err(e) => Err(CodeSelectionError(ConstEvalFailure(e)))
                            }
                        }
                    }
                }
            }
        }
    }
}


fn register_region_obligation<'tcx>(param_env: ty::ParamEnv<'tcx>,
                                    t_a: Ty<'tcx>,
                                    r_b: ty::Region<'tcx>,
                                    cause: ObligationCause<'tcx>,
                                    region_obligations: &mut NodeMap<Vec<RegionObligation<'tcx>>>)
{
    let region_obligation = RegionObligation { param_env,
                                               cause,
                                               sup_type: t_a,
                                               sub_region: r_b };

    debug!("register_region_obligation({:?}, cause={:?})",
           region_obligation, region_obligation.cause);

    region_obligations.entry(region_obligation.cause.body_id)
                      .or_insert(vec![])
                      .push(region_obligation);

}

fn to_fulfillment_error<'tcx>(
    error: Error<PendingPredicateAtomObligation<'tcx>, FulfillmentErrorCode<'tcx>>)
    -> FulfillmentError<'tcx>
{
    let obligation = error.backtrace.into_iter().next().unwrap().obligation;
    FulfillmentError::new(obligation, error.error)
}
