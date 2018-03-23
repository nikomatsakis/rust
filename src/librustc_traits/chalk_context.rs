use crate::lowering::Lower;

use chalk_engine::{context, ExClause, Literal, hh::HhGoal};

use rustc::{infer::canonical::{Canonical, CanonicalVarValues, QueryRegionConstraint, QueryResult},
            infer::{InferCtxt, InferOk, LateBoundRegionConversionTime},
            traits::{DomainGoal, Goal, ProgramClause, QuantifierKind}, ty::subst::Kind,
            ty::{self, TyCtxt}};

use std::fmt::Debug;

use syntax_pos::DUMMY_SP;

#[derive(Copy, Clone, Debug)]
crate struct ChalkContext<'cx, 'gcx: 'cx> {
    tcx: TyCtxt<'cx, 'gcx, 'gcx>,
}

#[derive(Copy, Clone)]
crate struct ChalkInferenceContext<'cx, 'gcx: 'tcx, 'tcx: 'cx> {
    infcx: &'cx InferCtxt<'cx, 'gcx, 'tcx>,
}

crate struct UniverseMap;

crate struct ConstrainedSubst<'tcx> {
    subst: CanonicalVarValues<'tcx>,
    constraints: Vec<QueryRegionConstraint<'tcx>>,
}

impl<'cx, 'gcx> context::Context for ChalkContext<'cx, 'gcx> {
    type CanonicalExClause = Canonical<'gcx, ExClause<Self>>;

    type CanonicalGoalInEnvironment = Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>>;

    // u-canonicalization not yet implemented
    type UCanonicalGoalInEnvironment = Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>>;

    type CanonicalConstrainedSubst = Canonical<'gcx, ConstrainedSubst<'gcx>>;

    // u-canonicalization not yet implemented
    type UniverseMap = UniverseMap;

    type Solution = Canonical<'gcx, QueryResult<'gcx, ()>>;
}

impl context::InferenceContext for ChalkInferenceContext<'cx, 'gcx, 'tcx> {
    type Environment = ty::ParamEnv<'tcx>;

    type Goal = Goal<'tcx>;

    type DomainGoal = DomainGoal<'tcx>;

    type GoalInEnvironment = ty::ParamEnvAnd<'tcx, Goal<'tcx>>;

    // should have an environment, but we don't handle that yet
    type RegionConstraint = QueryRegionConstraint<'tcx>;

    type Substitution = CanonicalVarValues<'tcx>;

    type BindersGoal = ty::Binder<Goal<'tcx>>;

    type Parameter = Kind<'tcx>;

    type ProgramClause = ProgramClause<'tcx>;

    type UnificationResult = InferOk<'tcx, ()>;
}

impl context::UCanonicalGoalInEnvironment<ChalkContext<'cx, 'gcx, 'tcx>>
    for Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>>
{
    fn canonical(&self) -> &Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>> {
        self
    }

    fn is_trivial_substitution(
        &self,
        canonical_subst: &Canonical<'tcx, ConstrainedSubst<'tcx>>,
    ) -> bool {
        let subst = &canonical_subst.value.subst;
        assert_eq!(self.canonical.variables.len(), subst.var_values.len());
        subst
            .var_values
            .iter_enumerated()
            .all(|(cvar, kind)| match kind.unpack() {
                Kind::Lifetime(r) => match r {
                    ty::ReCanonical(cvar1) => cvar == cvar1,
                    _ => false,
                },
                Kind::Type(ty) => match ty.sty {
                    ty::TyInfer(ty::InferTy::CanonicalTy(cvar1)) => cvar == cvar1,
                    _ => false,
                },
            })
    }

    fn num_universes(&self) -> usize {
        0 // FIXME
    }
}

impl context::GoalInEnvironment<ChalkContext<'cx, 'gcx, 'tcx>>
    for ty::ParamEnvAnd<'tcx, Goal<'tcx>>
{
    fn environment(&self) -> &ty::ParamEnv<'tcx> {
        &self.param_env
    }
}

impl context::UnificationOps<ChalkContext<'cx, 'gcx>, ChalkInferenceContext<'cx, 'gcx, 'tcx>>
    for InferCtxt<'cx, 'gcx, 'tcx>
{
    fn program_clauses(
        &self,
        environment: &ty::ParamEnv<'tcx>,
        goal: &DomainGoal<'tcx>,
    ) -> Vec<ProgramClause<'tcx>> {
        use rustc::traits::DomainGoal::*;
        use rustc::traits::WhereClauseAtom::*;

        match goal {
            Holds(Implemented(trait_predicate)) => {
                // These come from:
                //
                // - Trait definitions (implied bounds)
                // - Implementations of the trait itself
                panic!()
            }

            Holds(ProjectionEq(projection_predicate)) => {
                // These come from:
                panic!()
            }

            WellFormed(Implemented(trait_predicate)) => {
                // These come from -- the trait decl.
                panic!()
            }

            WellFormed(ProjectionEq(projection_predicate)) => {
                panic!()
            }

            FromEnv(Implemented(trait_predicate)) => {
                panic!()
            }

            FromEnv(ProjectionEq(projection_predicate)) => {
                panic!()
            }

            WellFormedTy(ty) => {
                panic!()
            }

            FromEnvTy(ty) => {
                panic!()
            }

            RegionOutlives(region_outlives) => {
                panic!()
            }

            TypeOutlives(type_outlives) => {
                panic!()
            }
        }
    }

    fn instantiate_binders_universally(&mut self, arg: &ty::Binder<Goal<'tcx>>) -> Goal<'tcx> {
        panic!("FIXME -- universal instantiation needs sgrif's branch")
    }

    fn instantiate_binders_existentially(&mut self, arg: &ty::Binder<Goal<'tcx>>) -> Goal<'tcx> {
        let (value, _map) = self.replace_late_bound_regions_with_fresh_var(
            DUMMY_SP,
            LateBoundRegionConversionTime::HigherRankedType,
            arg,
        );
        value
    }

    fn debug_ex_clause(
        &mut self,
        value: &'v ExClause<ChalkContext<'cx, 'gcx, 'tcx>>,
    ) -> Box<Debug + 'v> {
        Box::new(self.resolve_type_vars_if_possible(value))
    }

    fn canonicalize_goal(
        &mut self,
        value: &ty::ParamEnvAnd<'tcx, Goal<'tcx>>,
    ) -> Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>> {
        self.canonicalize_query(value).0
    }

    fn canonicalize_ex_clause(
        &mut self,
        value: &ExClause<ChalkContext<'cx, 'gcx, 'tcx>>,
    ) -> Canonical<'gcx, ExClause<ChalkContext<'cx, 'gcx, 'tcx>>> {
        self.canonicalize_response(value).0
    }

    fn canonicalize_constrained_subst(
        &mut self,
        subst: CanonicalVarValues<'tcx>,
        constraints: Vec<QueryRegionConstraint<'tcx>>,
    ) -> Canonical<'gcx, ConstrainedSubst<'gcx>> {
        self.canonicalize_response(&ConstrainedSubst { subst, constraints }).0
    }
}

impl context::Environment<ChalkContext<'cx, 'gcx, 'tcx>> for ty::ParamEnv<'tcx> {
    fn add_clauses(&self, clauses: impl IntoIterator<Item = DomainGoal<'tcx>>) -> Self {
        panic!("FIXME no method to add clauses to ParamEnv yet")
    }
}

impl context::CanonicalConstrainedSubst<ChalkContext<'cx, 'gcx>>
    for Canonical<'gcx, ConstrainedSubst<'gcx>>
{
    fn empty_constraints(&self) -> bool {
        self.value.constraints.is_empty()
    }
}

impl context::DomainGoal<ChalkContext<'cx, 'gcx>> for DomainGoal<'tcx> {
    fn into_goal(self) -> Goal<'tcx> {
        Goal::DomainGoal(self)
    }
}

impl context::Goal<ChalkContext<'cx, 'gcx>> for Goal<'tcx> {
    fn cannot_prove(self) -> Goal<'tcx> {
        Goal::CannotProve
    }

    fn into_hh_goal(self) -> HhGoal<ChalkContext<'cx, 'gcx, 'tcx>> {
        match self {
            Goal::Implies(..) => panic!("FIXME rust-lang-nursery/chalk#94"),
            Goal::And(left, right) => HhGoal::And(left, right),
            Goal::Not(left, right) => HhGoal::Not(left, right),
            Goal::DomainGoal(d) => HhGoal::DomainGoal(d),
            Goal::Quantified(QuantifierKind::Universal, binder) => HhGoal::ForAll(*binder),
            Goal::Quantified(QuantifierKind::Existential, binder) => HhGoal::Exists(*binder),
            Goal::CannotProve => HhGoal::CannotProve,
        }
    }
}

impl context::UniverseMap<ChalkContext<'cx, 'gcx, 'tcx>> for UniverseMap {
    fn map_goal_from_canonical(
        &self,
        value: &Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>>,
    ) -> Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>> {
        *value
    }

    fn map_subst_from_canonical(
        &self,
        value: &Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>>,
    ) -> Canonical<'gcx, ty::ParamEnvAnd<'gcx, Goal<'gcx>>> {
        *value
    }
}

impl context::UnificationResult<ChalkContext<'cx, 'gcx, 'tcx>> for InferOk<'tcx, ()> {
    fn into_ex_clause(self, ex_clause: &mut ExClause<ChalkContext<'cx, 'gcx, 'tcx>>) {
        ex_clause
            .subgoals
            .extend(self.into_obligations().into_iter().map(|obligation| {
                let param_env = obligation.param_env;
                let goal: Goal<'tcx> = obligation.predicate.lower();
                Literal::Positive(param_env.and(goal))
            }));
    }
}
