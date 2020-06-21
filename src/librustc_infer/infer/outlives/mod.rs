//! Various code related to computing outlives relations.

pub mod env;
pub mod obligations;
pub mod verify;

use rustc_middle::traits::query::OutlivesBound;
use rustc_middle::ty::{self, TyCtxt};

pub fn explicit_outlives_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
) -> impl Iterator<Item = OutlivesBound<'tcx>> + 'tcx {
    debug!("explicit_outlives_bounds()");
    param_env
        .caller_bounds
        .into_iter()
        .filter_map(move |pred| pred.ignore_qualifiers_with_unbound_vars(tcx).no_bound_vars())
        .filter_map(|pred| match pred.kind() {
            ty::PredicateKind::Projection(..)
            | ty::PredicateKind::Trait(..)
            | ty::PredicateKind::Subtype(..)
            | ty::PredicateKind::WellFormed(..)
            | ty::PredicateKind::ObjectSafe(..)
            | ty::PredicateKind::ClosureKind(..)
            | ty::PredicateKind::TypeOutlives(..)
            | ty::PredicateKind::ConstEvaluatable(..)
            | ty::PredicateKind::ConstEquate(..) => None,
            ty::PredicateKind::RegionOutlives(ty::OutlivesPredicate(r_a, r_b)) => {
                Some(OutlivesBound::RegionSubRegion(r_b, r_a))
            }
            ty::PredicateKind::ForAll(_) => bug!("unexpected_predicate: {:?}", pred),
        })
}
