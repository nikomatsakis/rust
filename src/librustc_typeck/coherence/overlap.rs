// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Overlap: No two impls for the same trait are implemented for the
//! same type.

use middle::cstore::CrateStore;
use middle::traits;
use middle::ty;
use syntax::ast;
use rustc::dep_graph::DepNode;
use rustc_front::hir;
use rustc_front::intravisit;
use util::nodemap::{DefIdMap, DefIdSet};

pub fn check(tcx: &ty::ctxt) {
    let mut overlap = OverlapChecker { tcx: tcx,
                                       traits_checked: DefIdSet(),
                                       default_impls: DefIdMap() };

    // this secondary walk specifically checks for some other cases,
    // like defaulted traits, for which additional overlap rules exist
    tcx.visit_all_items_in_krate(DepNode::CoherenceOverlapCheckSpecial, &mut overlap);
}

struct OverlapChecker<'cx, 'tcx:'cx> {
    tcx: &'cx ty::ctxt<'tcx>,

    // The set of traits where we have checked for overlap.  This is
    // used to avoid checking the same trait twice.
    //
    // NB. It's ok to skip tracking this set because we fully
    // encapsulate it, and we always create a task
    // (`CoherenceOverlapCheck`) corresponding to each entry.
    traits_checked: DefIdSet,

    // maps from a trait def-id to an impl id
    default_impls: DefIdMap<ast::NodeId>,
}

impl<'cx, 'tcx,'v> intravisit::Visitor<'v> for OverlapChecker<'cx, 'tcx> {
    fn visit_item(&mut self, item: &'v hir::Item) {
        match item.node {
            hir::ItemDefaultImpl(..) => {
                // look for another default impl; note that due to the
                // general orphan/coherence rules, it must always be
                // in this crate.
                let impl_def_id = self.tcx.map.local_def_id(item.id);
                let trait_ref = self.tcx.impl_trait_ref(impl_def_id).unwrap();

                self.check_for_overlapping_impls_of_trait(trait_ref.def_id);

                let prev_default_impl = self.default_impls.insert(trait_ref.def_id, item.id);
                if let Some(prev_id) = prev_default_impl {
                    span_err!(self.tcx.sess,
                              self.span_of_impl(impl_def_id), E0519,
                              "redundant default implementations of trait `{}`:",
                              trait_ref);
                    span_note!(self.tcx.sess,
                               self.span_of_impl(self.tcx.map.local_def_id(prev_id)),
                               "redundant implementation is here:");
                }
            }
            hir::ItemImpl(_, _, _, Some(_), ref self_ty, _) => {
                let impl_def_id = self.tcx.map.local_def_id(item.id);
                let trait_ref = self.tcx.impl_trait_ref(impl_def_id).unwrap();
                let trait_def_id = trait_ref.def_id;

                let _task = self.tcx.dep_graph.in_task(DepNode::CoherenceOverlapCheck(trait_def_id));

                let def = self.tcx.lookup_trait_def(trait_def_id);

                // attempt to insert into the specialization graph
                let insert_result = def.add_impl_for_specialization(self.tcx,
                                                                    impl_def_id,
                                                                    trait_ref);

                // insertion failed due to overlap
                if let Err(overlap) = insert_result {
                    // only print the Self type if it has at least some outer
                    // concrete shell; otherwise, it's not adding much
                    // information.
                    let self_type = {
                        overlap.on_trait_ref.substs.self_ty().and_then(|ty| {
                            if ty.has_concrete_skeleton() {
                                Some(format!(" for type `{}`", ty))
                            } else {
                                None
                            }
                        }).unwrap_or(String::new())
                    };

                    span_err!(self.tcx.sess, self.span_of_impl(impl_def_id), E0119,
                              "conflicting implementations of trait `{}`{}:",
                              overlap.on_trait_ref,
                              self_type);

                    match self.tcx.span_of_impl(overlap.with_impl) {
                        Ok(span) => {
                            span_note!(self.tcx.sess, span, "conflicting implementation is here:");
                        }
                        Err(cname) => {
                            self.tcx.sess.note(&format!("conflicting implementation in crate `{}`",
                                                        cname));
                        }
                    }
                }

                // check for overlap with the automatic `impl Trait for Trait`
                if let ty::TyTrait(ref data) = trait_ref.self_ty().sty {
                    // This is something like impl Trait1 for Trait2. Illegal
                    // if Trait1 is a supertrait of Trait2 or Trait2 is not object safe.

                    if !traits::is_object_safe(self.tcx, data.principal_def_id()) {
                        // This is an error, but it will be
                        // reported by wfcheck.  Ignore it
                        // here. This is tested by
                        // `coherence-impl-trait-for-trait-object-safe.rs`.
                    } else {
                        let mut supertrait_def_ids =
                            traits::supertrait_def_ids(self.tcx, data.principal_def_id());
                        if supertrait_def_ids.any(|d| d == trait_def_id) {
                            span_err!(self.tcx.sess, item.span, E0371,
                                      "the object type `{}` automatically \
                                       implements the trait `{}`",
                                      trait_ref.self_ty(),
                                      self.tcx.item_path_str(trait_def_id));
                        }
                    }
                }
            }
            _ => {}
        }
    }
}
