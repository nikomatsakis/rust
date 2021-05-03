//! Helper routines for higher-ranked things. See the `doc` module at
//! the end of the file for details.

use std::collections::BTreeMap;

use super::combine::CombineFields;
use super::{HigherRankedType, InferCtxt};

use crate::infer::CombinedSnapshot;
use rustc_middle::ty::relate::{Relate, RelateResult, TypeRelation};
use rustc_middle::ty::{self, Binder, TypeFoldable};

impl<'a, 'tcx> CombineFields<'a, 'tcx> {
    pub fn higher_ranked_sub<T>(
        &mut self,
        a: Binder<'tcx, T>,
        b: Binder<'tcx, T>,
        a_is_expected: bool,
    ) -> RelateResult<'tcx, Binder<'tcx, T>>
    where
        T: Relate<'tcx>,
    {
        debug!("higher_ranked_sub(a={:?}, b={:?})", a, b);

        // Rather than checking the subtype relationship between `a` and `b`
        // as-is, we need to do some extra work here in order to make sure
        // that function subtyping works correctly with respect to regions
        //
        // Note: this is a subtle algorithm.  For a full explanation, please see
        // the rustc dev guide:
        // <https://rustc-dev-guide.rust-lang.org/borrow_check/region_inference/placeholders_and_universes.html>

        let span = self.trace.cause.span;

        self.infcx.commit_if_ok(|_| {
            // First, we instantiate each bound region in the supertype with a
            // fresh placeholder region.
            let b_prime = self.infcx.replace_bound_vars_with_placeholders(b);

            // Next, we instantiate each bound region in the subtype
            // with a fresh region variable. These region variables --
            // but no other pre-existing region variables -- can name
            // the placeholders.
            let (a_prime, _) =
                self.infcx.replace_bound_vars_with_fresh_vars(span, HigherRankedType, a);

            debug!("a_prime={:?}", a_prime);
            debug!("b_prime={:?}", b_prime);

            // Compare types now that bound regions have been replaced.
            let result = self.sub(a_is_expected).relate(a_prime, b_prime)?;

            debug!("higher_ranked_sub: OK result={:?}", result);

            // We related `a_prime` and `b_prime`, which just had any bound vars
            // replaced with placeholders or infer vars, respectively. Relating
            // them should not introduce new bound vars.
            Ok(ty::Binder::dummy(result))
        })
    }
}

impl<'a, 'tcx> InferCtxt<'a, 'tcx> {
    /// Replaces all regions (resp. types) bound by `binder` with placeholder
    /// regions (resp. types) and return a map indicating which bound-region
    /// placeholder region. This is the first step of checking subtyping
    /// when higher-ranked things are involved.
    ///
    /// **Important:** You have to be careful to not leak these placeholders,
    /// for more information about how placeholders and HRTBs work, see
    /// the [rustc dev guide].
    ///
    /// [rustc dev guide]: https://rustc-dev-guide.rust-lang.org/traits/hrtb.html
    pub fn replace_bound_vars_with_placeholders<T>(&self, binder: ty::Binder<'tcx, T>) -> T
    where
        T: TypeFoldable<'tcx>,
    {
        self.replace_bound_vars_with_placeholders_mapped(binder).0
    }

    /// Like `replace_bound_vars_with_placeholders`, but also returns the
    /// `UniverseIndex` the new placeholder reside in.
    pub fn replace_bound_vars_with_placeholders_mapped<T>(&self, binder: ty::Binder<'tcx, T>)
        -> (
            T,
            BTreeMap<ty::PlaceholderRegion, ty::BoundRegion>,
            BTreeMap<ty::PlaceholderType, ty::BoundTy>,
            BTreeMap<ty::PlaceholderConst<'tcx>, ty::BoundVar>,
        )
    where
        T: TypeFoldable<'tcx>,
    {
        // Figure out what the next universe will be, but don't actually create
        // it until after we've done the substitution (in particular there may
        // be no bound variables). This is a performance optimization, since the
        // leak check for example can be skipped if no new universes are created
        // (i.e., if there are no placeholders).
        let next_universe = self.universe().next_universe();

        let mut mapped_regions: BTreeMap<ty::PlaceholderRegion, ty::BoundRegion> = BTreeMap::new();
        let mut mapped_types: BTreeMap<ty::PlaceholderType, ty::BoundTy> = BTreeMap::new();
        let mut mapped_consts: BTreeMap<ty::PlaceholderConst<'tcx>, ty::BoundVar> = BTreeMap::new();

        let fld_r = |br: ty::BoundRegion| {
            let p = ty::PlaceholderRegion {
                universe: next_universe,
                name: br.kind,
            };
            mapped_regions.insert(p, br);
            self.tcx.mk_region(ty::RePlaceholder(p))
        };

        let fld_t = |bound_ty: ty::BoundTy| {
            let p = ty::PlaceholderType {
                universe: next_universe,
                name: bound_ty.var,
            };
            mapped_types.insert(p, bound_ty);
            self.tcx.mk_ty(ty::Placeholder(p))
        };

        let fld_c = |bound_var: ty::BoundVar, ty| {
            let p = ty::PlaceholderConst {
                universe: next_universe,
                name: ty::BoundConst { var: bound_var, ty },
            };
            mapped_consts.insert(p, bound_var);
            self.tcx.mk_const(ty::Const {
                val: ty::ConstKind::Placeholder(p),
                ty,
            })
        };

        let (result, map) = self.tcx.replace_bound_vars(binder, fld_r, fld_t, fld_c);

        // If there were higher-ranked regions to replace, then actually create
        // the next universe (this avoids needlessly creating universes).
        if !map.is_empty() {
            let n_u = self.create_next_universe();
            assert_eq!(n_u, next_universe);
        }

        debug!(
            "replace_bound_vars_with_placeholders(\
             next_universe={:?}, \
             result={:?}, \
             map={:?})",
            next_universe, result, map,
        );

        (result, mapped_regions, mapped_types, mapped_consts)
    }

    /// See `infer::region_constraints::RegionConstraintCollector::leak_check`.
    pub fn leak_check(
        &self,
        overly_polymorphic: bool,
        snapshot: &CombinedSnapshot<'_, 'tcx>,
    ) -> RelateResult<'tcx, ()> {
        // If the user gave `-Zno-leak-check`, or we have been
        // configured to skip the leak check, then skip the leak check
        // completely. The leak check is deprecated. Any legitimate
        // subtyping errors that it would have caught will now be
        // caught later on, during region checking. However, we
        // continue to use it for a transition period.
        if self.tcx.sess.opts.debugging_opts.no_leak_check || self.skip_leak_check.get() {
            return Ok(());
        }

        self.inner.borrow_mut().unwrap_region_constraints().leak_check(
            self.tcx,
            overly_polymorphic,
            self.universe(),
            snapshot,
        )
    }
}
