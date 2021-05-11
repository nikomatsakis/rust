use std::{
    cell::{Cell, RefCell},
    fmt,
};

use rustc_data_structures::fx::FxHashMap;
use rustc_index::newtype_index;
use rustc_infer::traits::{EvaluationResult, TraitObligation};
use rustc_middle::ty;

newtype_index! {
    pub(super) struct Dfn {
        ENCODABLE = custom
        DEBUG_FORMAT = "Dfn({})"
    }
}
// A stack that walks back up the stack frame.
pub(super) struct TraitObligationStack<'prev, 'tcx> {
    pub(super) obligation: &'prev TraitObligation<'tcx>,

    /// The trait ref from `obligation` but "freshened" with the
    /// selection-context's freshener. Used to check for recursion.
    pub(super) fresh_trait_ref: ty::PolyTraitRef<'tcx>,

    /// Starts out equal to `depth` -- if, during evaluation, we
    /// encounter a cycle, then we will set this flag to the minimum
    /// depth of that cycle for all participants in the cycle. These
    /// participants will then forego caching their results. This is
    /// not the most efficient solution, but it addresses #60010. The
    /// problem we are trying to prevent:
    ///
    /// - If you have `A: AutoTrait` requires `B: AutoTrait` and `C: NonAutoTrait`
    /// - `B: AutoTrait` requires `A: AutoTrait` (coinductive cycle, ok)
    /// - `C: NonAutoTrait` requires `A: AutoTrait` (non-coinductive cycle, not ok)
    ///
    /// you don't want to cache that `B: AutoTrait` or `A: AutoTrait`
    /// is `EvaluatedToOk`; this is because they were only considered
    /// ok on the premise that if `A: AutoTrait` held, but we indeed
    /// encountered a problem (later on) with `A: AutoTrait. So we
    /// currently set a flag on the stack node for `B: AutoTrait` (as
    /// well as the second instance of `A: AutoTrait`) to suppress
    /// caching.
    ///
    /// This is a simple, targeted fix. A more-performant fix requires
    /// deeper changes, but would permit more caching: we could
    /// basically defer caching until we have fully evaluated the
    /// tree, and then cache the entire tree at once. In any case, the
    /// performance impact here shouldn't be so horrible: every time
    /// this is hit, we do cache at least one trait, so we only
    /// evaluate each member of a cycle up to N times, where N is the
    /// length of the cycle. This means the performance impact is
    /// bounded and we shouldn't have any terrible worst-cases.
    pub(super) reached_dfn: Cell<Dfn>,

    pub(super) previous: TraitObligationStackList<'prev, 'tcx>,

    /// The number of parent frames plus one (thus, the topmost frame has depth 1).
    pub(super) depth: usize,

    /// The depth-first number of this node in the search graph -- a
    /// pre-order index. Basically, a freshly incremented counter.
    pub(super) dfn: Dfn,
}

impl<'o, 'tcx> TraitObligationStack<'o, 'tcx> {
    pub(super) fn list(&'o self) -> TraitObligationStackList<'o, 'tcx> {
        TraitObligationStackList::with(self)
    }

    pub(super) fn cache(&self) -> &'o ProvisionalEvaluationCache<'tcx> {
        self.previous.cache
    }

    pub(super) fn iter(&'o self) -> TraitObligationStackList<'o, 'tcx> {
        self.list()
    }

    /// Indicates that attempting to evaluate this stack entry
    /// required accessing something from the stack at depth `reached_depth`.
    pub(super) fn update_reached_dfn(&self, reached_dfn: Dfn) {
        assert!(
            self.dfn > reached_dfn,
            "invoked `update_reached_depth` with something under this stack: \
             self.dfn={:?} reached_dfn={:?}",
            self.dfn,
            reached_dfn,
        );
        debug!(?reached_dfn, "update_reached_dfn");
        let mut p = self;
        while reached_dfn < p.dfn {
            debug!(?p.fresh_trait_ref, "update_reached_depth: marking as cycle participant");
            p.reached_dfn.set(p.reached_dfn.get().min(reached_dfn));
            p = p.previous.head.unwrap();
        }
    }
}

#[derive(Copy, Clone)]
pub(super) struct TraitObligationStackList<'o, 'tcx> {
    cache: &'o ProvisionalEvaluationCache<'tcx>,
    head: Option<&'o TraitObligationStack<'o, 'tcx>>,
}

impl<'o, 'tcx> TraitObligationStackList<'o, 'tcx> {
    pub(super) fn empty(
        cache: &'o ProvisionalEvaluationCache<'tcx>,
    ) -> TraitObligationStackList<'o, 'tcx> {
        TraitObligationStackList { cache, head: None }
    }

    pub(super) fn cache(&self) -> &'o ProvisionalEvaluationCache<'tcx> {
        self.cache
    }

    fn with(r: &'o TraitObligationStack<'o, 'tcx>) -> TraitObligationStackList<'o, 'tcx> {
        TraitObligationStackList { cache: r.cache(), head: Some(r) }
    }

    pub(super) fn head(&self) -> Option<&'o TraitObligationStack<'o, 'tcx>> {
        self.head
    }

    pub(super) fn depth(&self) -> usize {
        if let Some(head) = self.head { head.depth } else { 0 }
    }
}

impl<'o, 'tcx> Iterator for TraitObligationStackList<'o, 'tcx> {
    type Item = &'o TraitObligationStack<'o, 'tcx>;

    fn next(&mut self) -> Option<&'o TraitObligationStack<'o, 'tcx>> {
        let o = self.head?;
        *self = o.previous;
        Some(o)
    }
}

impl<'o, 'tcx> fmt::Debug for TraitObligationStackList<'o, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.into_iter()).finish()
    }
}

impl<'o, 'tcx> fmt::Debug for TraitObligationStack<'o, 'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "TraitObligationStack({:?})", self.obligation)
    }
}

/// The "provisional evaluation cache" is used to store intermediate cache results
/// when solving auto traits. Auto traits are unusual in that they can support
/// cycles. So, for example, a "proof tree" like this would be ok:
///
/// - `Foo<T>: Send` :-
///   - `Bar<T>: Send` :-
///     - `Foo<T>: Send` -- cycle, but ok
///   - `Baz<T>: Send`
///
/// Here, to prove `Foo<T>: Send`, we have to prove `Bar<T>: Send` and
/// `Baz<T>: Send`. Proving `Bar<T>: Send` in turn required `Foo<T>: Send`.
/// For non-auto traits, this cycle would be an error, but for auto traits (because
/// they are coinductive) it is considered ok.
///
/// However, there is a complication: at the point where we have
/// "proven" `Bar<T>: Send`, we have in fact only proven it
/// *provisionally*. In particular, we proved that `Bar<T>: Send`
/// *under the assumption* that `Foo<T>: Send`. But what if we later
/// find out this assumption is wrong?  Specifically, we could
/// encounter some kind of error proving `Baz<T>: Send`. In that case,
/// `Bar<T>: Send` didn't turn out to be true.
///
/// In Issue #60010, we found a bug in rustc where it would cache
/// these intermediate results. This was fixed in #60444 by disabling
/// *all* caching for things involved in a cycle -- in our example,
/// that would mean we don't cache that `Bar<T>: Send`.  But this led
/// to large slowdowns.
///
/// Specifically, imagine this scenario, where proving `Baz<T>: Send`
/// first requires proving `Bar<T>: Send` (which is true:
///
/// - `Foo<T>: Send` :-
///   - `Bar<T>: Send` :-
///     - `Foo<T>: Send` -- cycle, but ok
///   - `Baz<T>: Send`
///     - `Bar<T>: Send` -- would be nice for this to be a cache hit!
///     - `*const T: Send` -- but what if we later encounter an error?
///
/// The *provisional evaluation cache* resolves this issue. It stores
/// cache results that we've proven but which were involved in a cycle
/// in some way. We track the minimal stack depth (i.e., the
/// farthest from the top of the stack) that we are dependent on.
/// The idea is that the cache results within are all valid -- so long as
/// none of the nodes in between the current node and the node at that minimum
/// depth result in an error (in which case the cached results are just thrown away).
///
/// During evaluation, we consult this provisional cache and rely on
/// it. Accessing a cached value is considered equivalent to accessing
/// a result at `reached_depth`, so it marks the *current* solution as
/// provisional as well. If an error is encountered, we toss out any
/// provisional results added from the subtree that encountered the
/// error.  When we pop the node at `reached_depth` from the stack, we
/// can commit all the things that remain in the provisional cache.
pub(super) struct ProvisionalEvaluationCache<'tcx> {
    /// next "depth first number" to issue -- just a counter
    dfn: Cell<Dfn>,

    /// Map from cache key to the provisionally evaluated thing.
    /// The cache entries contain the result but also the DFN in which they
    /// were added. The DFN is used to clear out values on failure.
    ///
    /// Imagine we have a stack like:
    ///
    /// - `A B C` and we add a cache for the result of C (DFN 2)
    /// - Then we have a stack `A B D` where `D` has DFN 3
    /// - We try to solve D by evaluating E: `A B D E` (DFN 4)
    /// - `E` generates various cache entries which have cyclic dependices on `B`
    ///   - `A B D E F` and so forth
    ///   - the DFN of `F` for example would be 5
    /// - then we determine that `E` is in error -- we will then clear
    ///   all cache values whose DFN is >= 4 -- in this case, that
    ///   means the cached value for `F`.
    map: RefCell<FxHashMap<ty::PolyTraitRef<'tcx>, ProvisionalEvaluation>>,
}

/// A cache value for the provisional cache: contains the depth-first
/// number (DFN) and result.
#[derive(Copy, Clone, Debug)]
pub(super) struct ProvisionalEvaluation {
    pub(super) from_dfn: Dfn,
    pub(super) reached_dfn: Dfn,
    pub(super) result: EvaluationResult,
}

impl<'tcx> Default for ProvisionalEvaluationCache<'tcx> {
    fn default() -> Self {
        Self { dfn: Cell::new(Dfn::from(0_u32)), map: Default::default() }
    }
}

impl<'tcx> ProvisionalEvaluationCache<'tcx> {
    /// Get the next DFN in sequence (basically a counter).
    pub(super) fn next_dfn(&self) -> Dfn {
        let result = self.dfn.get();
        self.dfn.set(result + 1);
        result
    }

    /// Check the provisional cache for any result for
    /// `fresh_trait_ref`. If there is a hit, then you must consider
    /// it an access to the stack slots at depth
    /// `reached_depth` (from the returned value).
    pub(super) fn get_provisional(
        &self,
        fresh_trait_ref: ty::PolyTraitRef<'tcx>,
    ) -> Option<ProvisionalEvaluation> {
        debug!(
            ?fresh_trait_ref,
            "get_provisional = {:#?}",
            self.map.borrow().get(&fresh_trait_ref),
        );
        Some(self.map.borrow().get(&fresh_trait_ref)?.clone())
    }

    /// Insert a provisional result into the cache. The result came
    /// from the node with the given DFN. It accessed a minimum depth
    /// of `reached_depth` to compute. It evaluated `fresh_trait_ref`
    /// and resulted in `result`.
    pub(super) fn insert_provisional(
        &self,
        from_dfn: Dfn,
        reached_dfn: Dfn,
        fresh_trait_ref: ty::PolyTraitRef<'tcx>,
        result: EvaluationResult,
    ) {
        debug!(?from_dfn, ?fresh_trait_ref, ?result, "insert_provisional");
        self.map
            .borrow_mut()
            .insert(fresh_trait_ref, ProvisionalEvaluation { from_dfn, reached_dfn, result });
    }

    /// Invoked when the node with dfn `dfn` does not get a successful
    /// result.  This will clear out any provisional cache entries
    /// that were added since `dfn` was created. This is because the
    /// provisional entries are things which must assume that the
    /// things on the stack at the time of their creation succeeded --
    /// since the failing node is presently at the top of the stack,
    /// these provisional entries must either depend on it or some
    /// ancestor of it.
    pub(super) fn on_failure(&self, dfn: Dfn) {
        debug!(?dfn, "on_failure");
        self.map.borrow_mut().retain(|key, eval| {
            if eval.from_dfn >= dfn {
                debug!("on_failure: removing {:?}", key);
                false
            } else {
                true
            }
        });
    }

    /// Invoked when the node at depth `depth` completed without
    /// depending on anything higher in the stack (if that completion
    /// was a failure, then `on_failure` should have been invoked
    /// already). The callback `op` will be invoked for each
    /// provisional entry that we can now confirm.
    ///
    /// Note that we may still have provisional cache items remaining
    /// in the cache when this is done. For example, if there is a
    /// cycle:
    ///
    /// * A depends on...
    ///     * B depends on A
    ///     * C depends on...
    ///         * D depends on C
    ///     * ...
    ///
    /// Then as we complete the C node we will have a provisional cache
    /// with results for A, B, C, and D. This method would clear out
    /// the C and D results, but leave A and B provisional.
    ///
    /// This is determined based on the DFN: we remove any provisional
    /// results created since `dfn` started (e.g., in our example, dfn
    /// would be 2, representing the C node, and hence we would
    /// remove the result for D, which has DFN 3, but not the results for
    /// A and B, which have DFNs 0 and 1 respectively).
    pub(super) fn on_completion(
        &self,
        dfn: Dfn,
        mut op: impl FnMut(ty::PolyTraitRef<'tcx>, EvaluationResult),
    ) {
        debug!(?dfn, "on_completion");

        for (fresh_trait_ref, eval) in
            self.map.borrow_mut().drain_filter(|_k, eval| eval.from_dfn >= dfn)
        {
            debug!(?fresh_trait_ref, ?eval, "on_completion");

            // This result cannot have depended on anything that preceded `dfn`
            // or else `dfn` would not be complete:
            assert!(eval.reached_dfn >= dfn);

            op(fresh_trait_ref, eval.result);
        }
    }
}
