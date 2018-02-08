// Copyright 2012-2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use hir;
use hir::intravisit::{self, NestedVisitorMap, Visitor};
use util::nodemap::FxHashSet;

use super::NamedRegionMap;

pub(super) struct LateBoundDetector<'cx, 'tcx: 'cx> {}

struct ConstrainedNames {
    lifetimes: FxHashSet<hir::LifetimeName>,
    types: FxHashSet<Name>,
}

struct ConstrainedComputation<'cx, 'tcx> {
    tcx: TyCtxt<'cx, 'tcx, 'tcx>,

    /// In the "steady state", maps from the def-id of a type alias to
    /// a vector of indices. These indices indicate which of the
    /// lifetime parameters of the type alias are constrained.
    ///
    /// For example, if we have:
    ///
    ///     type Foo<'a> = &'a T
    ///
    /// then this would map to `vec![0]`.
    ///
    /// The map temporarily stores `None` while the values are being
    /// computed; this used to detect cycles. In the event that a
    /// cycle is uncovered, we assume all parameters are unconstrained
    /// for the cyclic case -- this will be an error later on anyhow.
    alias_cache: DefIdMap<Option<Vec<usize>>>,
}

struct ConstrainedVisitor<'cx, 'tcx: 'cx> {
    tcx: TyCtxt<'cx, 'tcx>,
    alias_cache: &mut DefIdMap<Option<Vec<usize>>>,
    constrained: &mut ConstrainedNames,
}

impl<'cx, 'tcx> ConstrainedVisitor<'cx, 'tcx> {
    fn constrained_by_ty(
        tcx: TyCtxt<'cx, 'tcx, 'tcx>,
        alias_cache: &mut DefIdMap<Option<Vec<usize>>>,
        ty: &hir::Ty,
    ) -> ConstrainedNames {
        let mut constrained = ConstrainedNames::default();
        ConstrainedVisitor {
            tcx,
            alias_cache,
            constrained: &mut constrained,
        }.from_ty(ty);
        constrained
    }

    fn from_ty<F>(&mut self, ty: &'tcx hir::Ty) {
        self.visit_ty(ty)
    }

    fn from_path<F>(&mut self, path: &'tcx hir::Path)
    where
        F: FnMut(&'tcx hir::Lifetime),
    {
        let indices;

        match path.def {
            Def::TyAlias(def_id) => {
                indices = self.compute_constrained_indices_of_type_alias(def_id);
                if let Some(last_segment) = path.segments.last() {
                    self.from_path_segment(last_segment, |i| indices.contains(&i));
                }
            }

            Def::Struct(_) | Def::Union(_) | Def::Trait(_) => {
                if let Some(last_segment) = path.segments.last() {
                    self.from_path_segment(
                        last_segment,
                        |_| true, // all indices
                    );
                }
            }

            Def::TyParam(_) => {}

            _ => return,
        }
    }

    fn from_type_alias(&mut self, def_id: DefId) -> Vec<usize> {
        if let Some(entry) = self.alias_cache.get(&def_id) {
            return entry.cloned().unwrap_or(vec![]);
        }

        // store placeholder to detect cycles
        self.alias_cache.insert(def_id, None);

        match &self.tcx.hir.expect_item(def_id).node {
            hir::ItemTy(ty, generics) => {
                // compute the names that are constrained in `ty`
                let constrained =
                    ConstrainedVisitor::constrained_by_ty(self.tcx, self.alias_cache, ty);

                // find the indices of those parameters that wound up being constrained
                let constrained_indices: Vec<usize> = generics
                    .params
                    .iter()
                    .enumerate()
                    .filter_map(|(index, param)| match param {
                        GenericParam::Lifetime(def) => {
                            if constrained_names.lifetimes.contains(&def.lifetime.name) {
                                Some(index)
                            } else {
                                None
                            }
                        }

                        GenericParam::Type(def) => {
                            if constrained_names.types.contains(&def.name) {
                                Some(index)
                            } else {
                                None
                            }
                        }
                    })
                    .collect();

                // update the alias cache
                let old = self.alias_cache.insert(Some(constrained_indices.clone()));
                assert!(old.is_none());

                constrained_indices
            }

            r => panic!(
                "compute_constrained_indices_of_type_alias invoked on non-alias: {:?}",
                r
            ),
        }
    }

    fn from_path_segment<F>(
        &mut self,
        path_segment: &'tcx hir::PathSegment,
        constrained: &mut ConstrainedNames,
        filter_fn: F,
    ) where
        F: Fn(usize) -> bool,
    {
        if let Some(parameters) = &path_segment.parameters {
            for (lifetime, index) in parameters.lifetimes.iter().zip(0..) {
                if filter_fn(index) {
                    constrained.lifetimes.insert(lifetime.name);
                }
            }

            let n = parameters.lifetimes.len();
            for (ty, index) in parameters.types.iter().zip(n..) {
                self.from_ty(ty, constrained);
            }
        }
    }
}

impl<'cx, 'tcx> Visitor<'tcx> for ConstrainedVisitor<'cx, 'tcx> {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'tcx> {
        NestedVisitorMap::None
    }

    fn visit_ty(&mut self, ty: &'tcx hir::Ty) {
        match ty.node {
            hir::TyPath(hir::QPath::Resolved(Some(_), _))
            | hir::TyPath(hir::QPath::TypeRelative(..)) => {
                // ignore lifetimes appearing in associated type
                // projections, as they are not *constrained*
                // (defined above)
            }

            hir::TyPath(hir::QPath::Resolved(None, ref path)) => {
                // consider only the lifetimes on the final
                // segment; I am not sure it's even currently
                // valid to have them elsewhere, but even if it
                // is, those would be potentially inputs to
                // projections
                if let Some(last_segment) = path.segments.last() {
                    self.from_path_segment(path.span, last_segment);
                }
            }

            _ => {
                intravisit::walk_ty(self, ty);
            }
        }
    }

    fn visit_lifetime(&mut self, lifetime_ref: &'tcx hir::Lifetime) {
        self.regions.insert(lifetime_ref.name);
    }
}

/// Detects late-bound lifetimes and inserts them into
/// `map.late_bound`.
///
/// A region declared on a fn is **late-bound** if:
/// - it is constrained by an argument type;
/// - it does not appear in a where-clause.
///
/// "Constrained" basically means that it appears in any type but
/// not amongst the inputs to a projection.  In other words, `<&'a
/// T as Trait<''b>>::Foo` does not constrain `'a` or `'b`.
pub(super) fn insert_late_bound_lifetimes(
    map: &mut NamedRegionMap,
    decl: &hir::FnDecl,
    generics: &hir::Generics,
) {
    debug!(
        "insert_late_bound_lifetimes(decl={:?}, generics={:?})",
        decl, generics
    );

    let mut constrained_by_input = ConstrainedCollector {
        regions: FxHashSet(),
    };
    for arg_ty in &decl.inputs {
        constrained_by_input.visit_ty(arg_ty);
    }

    let mut appears_in_output = AllCollector {
        regions: FxHashSet(),
    };
    intravisit::walk_fn_ret_ty(&mut appears_in_output, &decl.output);

    debug!(
        "insert_late_bound_lifetimes: constrained_by_input={:?}",
        constrained_by_input.regions
    );

    // Walk the lifetimes that appear in where clauses.
    //
    // Subtle point: because we disallow nested bindings, we can just
    // ignore binders here and scrape up all names we see.
    let mut appears_in_where_clause = AllCollector {
        regions: FxHashSet(),
    };

    for param in &generics.params {
        match *param {
            hir::GenericParam::Lifetime(ref lifetime_def) => {
                if !lifetime_def.bounds.is_empty() {
                    // `'a: 'b` means both `'a` and `'b` are referenced
                    appears_in_where_clause.visit_generic_param(param);
                }
            }
            hir::GenericParam::Type(ref ty_param) => {
                walk_list!(
                    &mut appears_in_where_clause,
                    visit_ty_param_bound,
                    &ty_param.bounds
                );
            }
        }
    }

    walk_list!(
        &mut appears_in_where_clause,
        visit_where_predicate,
        &generics.where_clause.predicates
    );

    debug!(
        "insert_late_bound_lifetimes: appears_in_where_clause={:?}",
        appears_in_where_clause.regions
    );

    // Late bound regions are those that:
    // - appear in the inputs
    // - do not appear in the where-clauses
    // - are not implicitly captured by `impl Trait`
    for lifetime in generics.lifetimes() {
        let name = lifetime.lifetime.name;

        // appears in the where clauses? early-bound.
        if appears_in_where_clause.regions.contains(&name) {
            continue;
        }

        // does not appear in the inputs, but appears in the return type? early-bound.
        if !constrained_by_input.regions.contains(&name)
            && appears_in_output.regions.contains(&name)
        {
            continue;
        }

        debug!(
            "insert_late_bound_lifetimes: \
             lifetime {:?} with id {:?} is late-bound",
            lifetime.lifetime.name, lifetime.lifetime.id
        );

        let inserted = map.late_bound.insert(lifetime.lifetime.id);
        assert!(
            inserted,
            "visited lifetime {:?} twice",
            lifetime.lifetime.id
        );
    }
}

struct ConstrainedCollector {
    regions: FxHashSet<hir::LifetimeName>,
}

impl<'v> Visitor<'v> for ConstrainedCollector {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'v> {
        NestedVisitorMap::None
    }

    fn visit_ty(&mut self, ty: &'v hir::Ty) {
        match &ty.node {
            hir::TyPath(hir::QPath::Resolved(Some(_), _))
            | hir::TyPath(hir::QPath::TypeRelative(..)) => {
                // ignore lifetimes appearing in associated type
                // projections, as they are not *constrained*
                // (defined above)
            }

            hir::TyPath(hir::QPath::Resolved(None, path)) => {
                // consider only the lifetimes on the final
                // segment; I am not sure it's even currently
                // valid to have them elsewhere, but even if it
                // is, those would be potentially inputs to
                // projections
                self.from_path(path);
            }

            _ => {
                intravisit::walk_ty(self, ty);
            }
        }
    }

    fn visit_lifetime(&mut self, lifetime_ref: &'v hir::Lifetime) {
        self.regions.insert(lifetime_ref.name);
    }
}

struct AllCollector {
    regions: FxHashSet<hir::LifetimeName>,
}

impl<'v> Visitor<'v> for AllCollector {
    fn nested_visit_map<'this>(&'this mut self) -> NestedVisitorMap<'this, 'v> {
        NestedVisitorMap::None
    }

    fn visit_lifetime(&mut self, lifetime_ref: &'v hir::Lifetime) {
        self.regions.insert(lifetime_ref.name);
    }
}
