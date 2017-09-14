// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use hir::def_id::DefId;
use ty::subst::{Subst, Substs};
use ty::{self, ToPredicate, ToPredicateAtom, Ty, TyCtxt};
use ty::outlives::Component;
use util::nodemap::FxHashSet;
use hir::{self};
use traits::specialize::specialization_graph::NodeItem;

use super::{Obligation, ObligationCause, PredicateObligation, SelectionContext, Normalized};

fn anonymize_predicate<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>,
                                       pred: &ty::Predicate<'tcx>)
                                       -> ty::Predicate<'tcx> {
    match *pred {
        ty::Predicate::Poly(ref binder) =>
            ty::Predicate::Poly(tcx.anonymize_late_bound_regions(binder)),

        ty::Predicate::Atom(atom) =>
            ty::Predicate::Atom(atom),
    }
}

struct PredicateSet<'a, 'gcx: 'a+'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    set: FxHashSet<ty::Predicate<'tcx>>,
}

impl<'a, 'gcx, 'tcx> PredicateSet<'a, 'gcx, 'tcx> {
    fn new(tcx: TyCtxt<'a, 'gcx, 'tcx>) -> PredicateSet<'a, 'gcx, 'tcx> {
        PredicateSet { tcx: tcx, set: FxHashSet() }
    }

    fn insert(&mut self, pred: &ty::Predicate<'tcx>) -> bool {
        // We have to be careful here because we want
        //
        //    for<'a> Foo<&'a int>
        //
        // and
        //
        //    for<'b> Foo<&'b int>
        //
        // to be considered equivalent. So normalize all late-bound
        // regions before we throw things into the underlying set.
        self.set.insert(anonymize_predicate(self.tcx, pred))
    }
}

///////////////////////////////////////////////////////////////////////////
// `Elaboration` iterator
///////////////////////////////////////////////////////////////////////////

/// "Elaboration" is the process of identifying all the predicates that
/// are implied by a source predicate. Currently this basically means
/// walking the "supertraits" and other similar assumptions. For
/// example, if we know that `T : Ord`, the elaborator would deduce
/// that `T : PartialOrd` holds as well. Similarly, if we have `trait
/// Foo : 'static`, and we know that `T : Foo`, then we know that `T :
/// 'static`.
pub struct Elaborator<'a, 'gcx: 'a+'tcx, 'tcx: 'a> {
    stack: Vec<ty::Predicate<'tcx>>,
    visited: PredicateSet<'a, 'gcx, 'tcx>,
}

pub fn elaborate_trait_ref<'cx, 'gcx, 'tcx>(
    tcx: TyCtxt<'cx, 'gcx, 'tcx>,
    trait_ref: ty::PolyTraitRef<'tcx>)
    -> Elaborator<'cx, 'gcx, 'tcx>
{
    elaborate_predicates(tcx, vec![trait_ref.to_predicate()])
}

pub fn elaborate_trait_refs<'cx, 'gcx, 'tcx>(
    tcx: TyCtxt<'cx, 'gcx, 'tcx>,
    trait_refs: &[ty::PolyTraitRef<'tcx>])
    -> Elaborator<'cx, 'gcx, 'tcx>
{
    let predicates = trait_refs.iter()
                               .map(|trait_ref| trait_ref.to_predicate())
                               .collect();
    elaborate_predicates(tcx, predicates)
}

pub fn elaborate_predicates<'cx, 'gcx, 'tcx>(
    tcx: TyCtxt<'cx, 'gcx, 'tcx>,
    mut predicates: Vec<ty::Predicate<'tcx>>)
    -> Elaborator<'cx, 'gcx, 'tcx>
{
    let mut visited = PredicateSet::new(tcx);
    predicates.retain(|pred| visited.insert(pred));
    Elaborator { stack: predicates, visited: visited }
}

impl<'cx, 'gcx, 'tcx> Elaborator<'cx, 'gcx, 'tcx> {
    pub fn filter_to_traits(self) -> FilterToTraits<'cx, 'gcx, 'tcx> {
        FilterToTraits::new(self.visited.tcx, self)
    }

    fn push(&mut self, predicate: &ty::Predicate<'tcx>) {
        let tcx = self.visited.tcx;

        // We don't elaborate all kinds of predicates. Also, the
        // treatment of binders can be a touch tricky here (in
        // particular, we can't just skolemize and recurse). So don't
        // do a general match on the kind of predicate, instead try to
        // convert to more narrow poly-things.

        // Elaborate `T: Foo` to include where-clauses declared on trait `Foo`.
        if let Some(data) = predicate.poly_trait(tcx) {
            let predicates = tcx.super_predicates_of(data.def_id());

            let mut predicates: Vec<_> =
                predicates.predicates
                          .iter()
                          .map(|p| p.subst_supertrait(tcx, data))
                          .collect();

            debug!("super_predicates: data={:?} predicates={:?}",
                   data, predicates);

            // Only keep those bounds that we haven't already
            // seen.  This is necessary to prevent infinite
            // recursion in some cases.  One common case is when
            // people define `trait Sized: Sized { }` rather than `trait
            // Sized { }`.
            predicates.retain(|r| self.visited.insert(r));

            self.stack.extend(predicates);
        }

        // Elaborate `T: 'a` to include other outlives relationships.
        //
        // e.g., `&'a i32: 'b` implies that `'a: 'b`.
        if let Some(data) = predicate.poly_type_outlives(tcx) {
            // We know that `T: 'a` for some type `T`. We can
            // often elaborate this. For example, if we know that
            // `[U]: 'a`, that implies that `U: 'a`. Similarly, if
            // we know `&'a U: 'b`, then we know that `'a: 'b` and
            // `U: 'b`.
            //
            // We can basically ignore bound regions here. So for
            // example `for<'c> Foo<'a,'c>: 'b` can be elaborated to
            // `'a: 'b`.

            // Ignore `for<'a> T: 'a` -- we might in the future
            // consider this as evidence that `T: 'static`, but
            // I'm a bit wary of such constructions and so for now
            // I want to be conservative. --nmatsakis
            let ty_max = data.skip_binder().0;
            let r_min = data.skip_binder().1;
            if r_min.is_late_bound() {
                return;
            }

            let visited = &mut self.visited;
            self.stack.extend(
                tcx.outlives_components(ty_max)
                   .into_iter()
                   .filter_map(|component| match component {
                       Component::Region(r) => if r.is_late_bound() {
                           None
                       } else {
                           Some(ty::OutlivesPredicate(r, r_min).to_predicate_atom())
                       },

                       Component::Param(p) => {
                           let ty = tcx.mk_param(p.idx, p.name);
                           Some(ty::OutlivesPredicate(ty, r_min).to_predicate_atom())
                       },

                       Component::UnresolvedInferenceVariable(_) => {
                           None
                       },

                       Component::Projection(_) |
                       Component::EscapingProjection(_) => {
                           // We can probably do more here. This
                           // corresponds to a case like `<T as
                           // Foo<'a>>::U: 'b`.
                           None
                       },
                   })
                   .map(|atom| atom.to_predicate())
                   .filter(|p| visited.insert(p)));
        }
    }
}

impl<'cx, 'gcx, 'tcx> Iterator for Elaborator<'cx, 'gcx, 'tcx> {
    type Item = ty::Predicate<'tcx>;

    fn next(&mut self) -> Option<ty::Predicate<'tcx>> {
        // Extract next item from top-most stack frame, if any.
        let next_predicate = match self.stack.pop() {
            Some(predicate) => predicate,
            None => {
                // No more stack frames. Done.
                return None;
            }
        };
        self.push(&next_predicate);
        return Some(next_predicate);
    }
}

///////////////////////////////////////////////////////////////////////////
// Supertrait iterator
///////////////////////////////////////////////////////////////////////////

pub type Supertraits<'cx, 'gcx, 'tcx> = FilterToTraits<'cx, 'gcx, 'tcx>;

pub fn supertraits<'cx, 'gcx, 'tcx>(tcx: TyCtxt<'cx, 'gcx, 'tcx>,
                                    trait_ref: ty::PolyTraitRef<'tcx>)
                                    -> Supertraits<'cx, 'gcx, 'tcx>
{
    elaborate_trait_ref(tcx, trait_ref).filter_to_traits()
}

pub fn transitive_bounds<'cx, 'gcx, 'tcx>(tcx: TyCtxt<'cx, 'gcx, 'tcx>,
                                          bounds: &[ty::PolyTraitRef<'tcx>])
                                          -> Supertraits<'cx, 'gcx, 'tcx>
{
    elaborate_trait_refs(tcx, bounds).filter_to_traits()
}

///////////////////////////////////////////////////////////////////////////
// Iterator over def-ids of supertraits

pub struct SupertraitDefIds<'a, 'gcx: 'a+'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    stack: Vec<DefId>,
    visited: FxHashSet<DefId>,
}

pub fn supertrait_def_ids<'cx, 'gcx, 'tcx>(tcx: TyCtxt<'cx, 'gcx, 'tcx>,
                                           trait_def_id: DefId)
                                           -> SupertraitDefIds<'cx, 'gcx, 'tcx>
{
    SupertraitDefIds {
        tcx,
        stack: vec![trait_def_id],
        visited: Some(trait_def_id).into_iter().collect(),
    }
}

impl<'cx, 'gcx, 'tcx> Iterator for SupertraitDefIds<'cx, 'gcx, 'tcx> {
    type Item = DefId;

    fn next(&mut self) -> Option<DefId> {
        let def_id = match self.stack.pop() {
            Some(def_id) => def_id,
            None => { return None; }
        };

        let tcx = self.tcx;
        let predicates = tcx.super_predicates_of(def_id);
        let visited = &mut self.visited;
        self.stack.extend(
            predicates.predicates
                      .iter()
                      .filter_map(|p| p.poly_trait(tcx))
                      .map(|t| t.def_id())
                      .filter(|&super_def_id| visited.insert(super_def_id)));
        Some(def_id)
    }
}

///////////////////////////////////////////////////////////////////////////
// Other
///////////////////////////////////////////////////////////////////////////

/// A filter around an iterator of predicates that makes it yield up
/// just trait references.
pub struct FilterToTraits<'cx, 'gcx: 'tcx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'gcx, 'tcx>,
    base_iterator: Elaborator<'cx, 'gcx, 'tcx>,
}

impl<'cx, 'gcx, 'tcx> FilterToTraits<'cx, 'gcx, 'tcx> {
    fn new(tcx: TyCtxt<'cx, 'gcx, 'tcx>,
           base_iterator: Elaborator<'cx, 'gcx, 'tcx>)
           -> Self {
        FilterToTraits { tcx, base_iterator }
    }
}

impl<'cx, 'gcx, 'tcx> Iterator for FilterToTraits<'cx, 'gcx, 'tcx> {
    type Item = ty::PolyTraitRef<'tcx>;

    fn next(&mut self) -> Option<ty::PolyTraitRef<'tcx>> {
        loop {
            match self.base_iterator.next() {
                None => return None,
                Some(predicate) => {
                    if let Some(trait_ref) = predicate.poly_trait(self.tcx) {
                        return Some(trait_ref);
                    }
                }
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// Other
///////////////////////////////////////////////////////////////////////////

/// Instantiate all bound parameters of the impl with the given substs,
/// returning the resulting trait ref and all obligations that arise.
/// The obligations are closed under normalization.
pub fn impl_trait_ref_and_oblig<'a, 'gcx, 'tcx>(selcx: &mut SelectionContext<'a, 'gcx, 'tcx>,
                                                param_env: ty::ParamEnv<'tcx>,
                                                impl_def_id: DefId,
                                                impl_substs: &Substs<'tcx>)
                                                -> (ty::TraitRef<'tcx>,
                                                    Vec<PredicateObligation<'tcx>>)
{
    let impl_trait_ref =
        selcx.tcx().impl_trait_ref(impl_def_id).unwrap();
    let impl_trait_ref =
        impl_trait_ref.subst(selcx.tcx(), impl_substs);
    let Normalized { value: impl_trait_ref, obligations: normalization_obligations1 } =
        super::normalize(selcx, param_env, ObligationCause::dummy(), &impl_trait_ref);

    let predicates = selcx.tcx().predicates_of(impl_def_id);
    let predicates = predicates.instantiate(selcx.tcx(), impl_substs);
    let Normalized { value: predicates, obligations: normalization_obligations2 } =
        super::normalize(selcx, param_env, ObligationCause::dummy(), &predicates);
    let impl_obligations =
        predicates_for_generics(ObligationCause::dummy(), 0, param_env, &predicates);

    let impl_obligations: Vec<_> =
        impl_obligations.into_iter()
        .chain(normalization_obligations1)
        .chain(normalization_obligations2)
        .collect();

    (impl_trait_ref, impl_obligations)
}

/// See `super::obligations_for_generics`
pub fn predicates_for_generics<'tcx>(cause: ObligationCause<'tcx>,
                                     recursion_depth: usize,
                                     param_env: ty::ParamEnv<'tcx>,
                                     generic_bounds: &ty::InstantiatedPredicates<'tcx>)
                                     -> Vec<PredicateObligation<'tcx>>
{
    debug!("predicates_for_generics(generic_bounds={:?})",
           generic_bounds);

    generic_bounds.predicates.iter().map(|predicate| {
        Obligation { cause: cause.clone(),
                     recursion_depth,
                     param_env,
                     predicate: predicate.clone() }
    }).collect()
}

pub fn predicate_for_trait_ref<'tcx>(
    cause: ObligationCause<'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
    recursion_depth: usize)
    -> PredicateObligation<'tcx>
{
    Obligation {
        cause,
        param_env,
        recursion_depth,
        predicate: trait_ref.to_predicate(),
    }
}

impl<'a, 'gcx, 'tcx> TyCtxt<'a, 'gcx, 'tcx> {
    pub fn predicate_for_trait_def(self,
                                   param_env: ty::ParamEnv<'tcx>,
                                   cause: ObligationCause<'tcx>,
                                   trait_def_id: DefId,
                                   recursion_depth: usize,
                                   param_ty: Ty<'tcx>,
                                   ty_params: &[Ty<'tcx>])
        -> PredicateObligation<'tcx>
    {
        let trait_ref = ty::TraitRef {
            def_id: trait_def_id,
            substs: self.mk_substs_trait(param_ty, ty_params)
        };
        predicate_for_trait_ref(cause, param_env, trait_ref, recursion_depth)
    }

    /// Cast a trait reference into a reference to one of its super
    /// traits; returns `None` if `target_trait_def_id` is not a
    /// supertrait.
    pub fn upcast_choices(self,
                          source_trait_ref: ty::PolyTraitRef<'tcx>,
                          target_trait_def_id: DefId)
                          -> Vec<ty::PolyTraitRef<'tcx>>
    {
        if source_trait_ref.def_id() == target_trait_def_id {
            return vec![source_trait_ref]; // shorcut the most common case
        }

        supertraits(self, source_trait_ref)
            .filter(|r| r.def_id() == target_trait_def_id)
            .collect()
    }

    /// Given a trait `trait_ref`, returns the number of vtable entries
    /// that come from `trait_ref`, excluding its supertraits. Used in
    /// computing the vtable base for an upcast trait of a trait object.
    pub fn count_own_vtable_entries(self, trait_ref: ty::PolyTraitRef<'tcx>) -> usize {
        let mut entries = 0;
        // Count number of methods and add them to the total offset.
        // Skip over associated types and constants.
        for trait_item in self.associated_items(trait_ref.def_id()) {
            if trait_item.kind == ty::AssociatedKind::Method {
                entries += 1;
            }
        }
        entries
    }

    /// Given an upcast trait object described by `object`, returns the
    /// index of the method `method_def_id` (which should be part of
    /// `object.upcast_trait_ref`) within the vtable for `object`.
    pub fn get_vtable_index_of_object_method<N>(self,
                                                object: &super::VtableObjectData<'tcx, N>,
                                                method_def_id: DefId) -> usize {
        // Count number of methods preceding the one we are selecting and
        // add them to the total offset.
        // Skip over associated types and constants.
        let mut entries = object.vtable_base;
        for trait_item in self.associated_items(object.upcast_trait_ref.def_id()) {
            if trait_item.def_id == method_def_id {
                // The item with the ID we were given really ought to be a method.
                assert_eq!(trait_item.kind, ty::AssociatedKind::Method);
                return entries;
            }
            if trait_item.kind == ty::AssociatedKind::Method {
                entries += 1;
            }
        }

        bug!("get_vtable_index_of_object_method: {:?} was not found",
             method_def_id);
    }

    pub fn closure_trait_ref_and_return_type(self,
        fn_trait_def_id: DefId,
        self_ty: Ty<'tcx>,
        sig: ty::PolyFnSig<'tcx>,
        tuple_arguments: TupleArgumentsFlag)
        -> ty::Binder<(ty::TraitRef<'tcx>, Ty<'tcx>)>
    {
        let arguments_tuple = match tuple_arguments {
            TupleArgumentsFlag::No => sig.skip_binder().inputs()[0],
            TupleArgumentsFlag::Yes =>
                self.intern_tup(sig.skip_binder().inputs(), false),
        };
        let trait_ref = ty::TraitRef {
            def_id: fn_trait_def_id,
            substs: self.mk_substs_trait(self_ty, &[arguments_tuple]),
        };
        ty::Binder((trait_ref, sig.skip_binder().output()))
    }

    pub fn generator_trait_ref_and_outputs(self,
        fn_trait_def_id: DefId,
        self_ty: Ty<'tcx>,
        sig: ty::PolyGenSig<'tcx>)
        -> ty::Binder<(ty::TraitRef<'tcx>, Ty<'tcx>, Ty<'tcx>)>
    {
        let trait_ref = ty::TraitRef {
            def_id: fn_trait_def_id,
            substs: self.mk_substs_trait(self_ty, &[]),
        };
        ty::Binder((trait_ref, sig.skip_binder().yield_ty, sig.skip_binder().return_ty))
    }

    pub fn impl_is_default(self, node_item_def_id: DefId) -> bool {
        match self.hir.as_local_node_id(node_item_def_id) {
            Some(node_id) => {
                let item = self.hir.expect_item(node_id);
                if let hir::ItemImpl(_, _, defaultness, ..) = item.node {
                    defaultness.is_default()
                } else {
                    false
                }
            }
            None => {
                self.global_tcx()
                    .impl_defaultness(node_item_def_id)
                    .is_default()
            }
        }
    }

    pub fn impl_item_is_final(self, node_item: &NodeItem<hir::Defaultness>) -> bool {
        node_item.item.is_final() && !self.impl_is_default(node_item.node.def_id())
    }
}

pub enum TupleArgumentsFlag { Yes, No }
