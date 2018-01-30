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
                    self.visit_path_segment(path.span, last_segment);
                }
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
