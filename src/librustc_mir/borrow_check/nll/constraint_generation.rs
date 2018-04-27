// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::{BorrowRegionVid, BorrowSet};
use borrow_check::location::LocationTable;
use borrow_check::nll::facts::AllFacts;
use rustc::hir;
use rustc::infer::InferCtxt;
use rustc::mir::visit::TyContext;
use rustc::mir::visit::{PlaceContext, Visitor};
use rustc::mir::Place::Projection;
use rustc::mir::{BasicBlock, BasicBlockData, Location, Mir, Place, RETURN_PLACE, Rvalue};
use rustc::mir::{Local, LocalDecl, PlaceProjection, ProjectionElem, Statement, Terminator};
use rustc::ty::fold::TypeFoldable;
use rustc::ty::subst::Substs;
use rustc::ty::{self, CanonicalTy, ClosureSubsts};

use super::region_infer::{Cause, RegionInferenceContext};
use super::ToRegionVid;

pub(super) fn generate_constraints<'cx, 'gcx, 'tcx>(
    infcx: &InferCtxt<'cx, 'gcx, 'tcx>,
    regioncx: &mut RegionInferenceContext<'tcx>,
    all_facts: &mut AllFacts,
    location_table: &LocationTable,
    mir: &Mir<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
) {
    let mut cg = ConstraintGeneration {
        borrow_set,
        infcx,
        regioncx,
        location_table,
        all_facts,
        mir,
    };

    // Hack: make `_0` live. I think ideally we'd just give it the
    // user declared type, really, along with the other
    // parameters. The problem is that right now when you have `_0 =
    // ...`, it winds up making `_0` be considered dead until then,
    // which means that we don't connect the universal regions in the
    // type of `_0` to anything. This would be correct if `_0` were an
    // ordinary variable, but it's not.
    //
    // Alternatively: if we had some way to make a "pan-location" for
    // the outlives relation (which wouldn't be too hard to do, I
    // don't think) then we could relate the types with *that*
    // "pan-location". This may be needed to support user-defined
    // types as well.
    cg.all_facts.use_live.extend(
        location_table
            .all_points()
            .map(|location| (RETURN_PLACE, location)),
    );

    for (local, local_decl) in mir.local_decls.iter_enumerated() {
        cg.visit_local_decl(local, local_decl);
    }

    for (bb, data) in mir.basic_blocks().iter_enumerated() {
        cg.visit_basic_block_data(bb, data);
    }
}

/// 'cg = the duration of the constraint generation process itself.
struct ConstraintGeneration<'cg, 'cx: 'cg, 'gcx: 'tcx, 'tcx: 'cx> {
    infcx: &'cg InferCtxt<'cx, 'gcx, 'tcx>,
    all_facts: &'cg mut AllFacts,
    location_table: &'cg LocationTable,
    regioncx: &'cg mut RegionInferenceContext<'tcx>,
    mir: &'cg Mir<'tcx>,
    borrow_set: &'cg BorrowSet<'tcx>,
}

impl<'cg, 'cx, 'gcx, 'tcx> Visitor<'tcx> for ConstraintGeneration<'cg, 'cx, 'gcx, 'tcx> {
    fn visit_basic_block_data(&mut self, bb: BasicBlock, data: &BasicBlockData<'tcx>) {
        self.super_basic_block_data(bb, data);
    }

    /// We sometimes have `substs` within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_substs(&mut self, substs: &&'tcx Substs<'tcx>, location: Location) {
        self.add_regular_live_constraint(*substs, location, Cause::LiveOther(location));
        self.super_substs(substs);
    }

    /// We sometimes have `region` within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_region(&mut self, region: &ty::Region<'tcx>, location: Location) {
        self.add_regular_live_constraint(*region, location, Cause::LiveOther(location));
        self.super_region(region);
    }

    /// We sometimes have `ty` within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_ty(&mut self, ty: &ty::Ty<'tcx>, ty_context: TyContext) {
        match ty_context {
            TyContext::ReturnTy(source_info)
            | TyContext::YieldTy(source_info)
            | TyContext::LocalDecl { source_info, .. } => {
                span_bug!(
                    source_info.span,
                    "should not be visiting outside of the CFG: {:?}",
                    ty_context
                );
            }
            TyContext::Location(location) => {
                self.add_regular_live_constraint(*ty, location, Cause::LiveOther(location));
            }
        }

        self.super_ty(ty);
    }

    fn visit_local_decl(&mut self, local: Local, local_decl: &LocalDecl<'tcx>) {
        self.infcx.tcx.for_each_free_region(&local_decl.ty, |r| {
            self.all_facts.use_region.push((local, r.to_region_vid()));
        });

        // Note: we do NOT invoke `super_local_decl` on purpose. We
        // don't want to visit the types and so forth outside of the
        // context of the control-flow graph.
    }

    /// We sometimes have `closure_substs` within an rvalue, or within a
    /// call. Make them live at the location where they appear.
    fn visit_closure_substs(&mut self, substs: &ClosureSubsts<'tcx>, location: Location) {
        self.add_regular_live_constraint(*substs, location, Cause::LiveOther(location));
        self.super_closure_substs(substs);
    }

    fn visit_statement(
        &mut self,
        block: BasicBlock,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.all_facts.cfg_edge.push((
            self.location_table.start_index(location),
            self.location_table.mid_index(location),
        ));

        self.all_facts.cfg_edge.push((
            self.location_table.mid_index(location),
            self.location_table
                .start_index(location.successor_within_block()),
        ));

        self.super_statement(block, statement, location);
    }

    fn visit_assign(
        &mut self,
        block: BasicBlock,
        place: &Place<'tcx>,
        rvalue: &Rvalue<'tcx>,
        location: Location,
    ) {
        // When we see `X = ...`, then kill borrows of
        // `(*X).foo` and so forth.
        if let Place::Local(temp) = place {
            if let Some(borrow_indices) = self.borrow_set.local_map.get(temp) {
                for &borrow_index in borrow_indices {
                    let borrow_data = &self.borrow_set[borrow_index];
                    let borrow_region = BorrowRegionVid {
                        region_vid: borrow_data.region.to_region_vid(),
                    };
                    let location_index = self.location_table.mid_index(location);
                    self.all_facts.killed.push((borrow_region, location_index));
                }
            }
        }

        self.super_assign(block, place, rvalue, location);
    }

    fn visit_terminator(
        &mut self,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        self.all_facts.cfg_edge.push((
            self.location_table.start_index(location),
            self.location_table.mid_index(location),
        ));

        for successor_block in terminator.successors().iter() {
            self.all_facts.cfg_edge.push((
                self.location_table.mid_index(location),
                self.location_table
                    .start_index(successor_block.start_location()),
            ));
        }

        self.super_terminator(block, terminator, location);
    }

    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        debug!("visit_rvalue(rvalue={:?}, location={:?})", rvalue, location);

        match rvalue {
            Rvalue::Ref(region, borrow_kind, borrowed_place) => {
                let region_vid = self.regioncx.to_region_vid(region);
                self.all_facts.borrow_region.push((
                    region_vid,
                    BorrowRegionVid { region_vid },
                    self.location_table.mid_index(location),
                ));

                // Look for an rvalue like:
                //
                //     & L
                //
                // where L is the path that is borrowed. In that case, we have
                // to add the reborrow constraints (which don't fall out
                // naturally from the type-checker).
                self.add_reborrow_constraint(location, region, borrowed_place);

                // Subtle: we do not invoke `visit_region` on
                // `region`. This is because it would introduce a
                // *liveness* constraint on `region`, but that would
                // actually be incorrect -- unlike every other case,
                // `&'x foo` is effectively a *def* of `region`.  That
                // is, executing `&'x foo` does not potentially read
                // the data that references of type `&'x T` may carry
                // on entry.

                self.visit_place(
                    borrowed_place,
                    PlaceContext::Borrow {
                        region: *region,
                        kind: *borrow_kind,
                    },
                    location,
                );
            }

            _ => {
                self.super_rvalue(rvalue, location);
            }
        }
    }

    fn visit_user_assert_ty(
        &mut self,
        _c_ty: &CanonicalTy<'tcx>,
        _local: &Local,
        _location: Location,
    ) {
    }
}

impl<'cx, 'cg, 'gcx, 'tcx> ConstraintGeneration<'cx, 'cg, 'gcx, 'tcx> {
    /// Some variable with type `live_ty` is "regular live" at
    /// `location` -- i.e., it may be used later. This means that all
    /// regions appearing in the type `live_ty` must be live at
    /// `location`.
    fn add_regular_live_constraint<T>(&mut self, live_ty: T, location: Location, cause: Cause)
    where
        T: TypeFoldable<'tcx>,
    {
        debug!(
            "add_regular_live_constraint(live_ty={:?}, location={:?})",
            live_ty, location
        );

        self.infcx
            .tcx
            .for_each_free_region(&live_ty, |live_region| {
                let vid = live_region.to_region_vid();
                self.regioncx.add_live_point(vid, location, &cause);
            });
    }

    // Add the reborrow constraint at `location` so that `borrowed_place`
    // is valid for `borrow_region`.
    fn add_reborrow_constraint(
        &mut self,
        location: Location,
        borrow_region: ty::Region<'tcx>,
        borrowed_place: &Place<'tcx>,
    ) {
        let mut borrowed_place = borrowed_place;

        debug!(
            "add_reborrow_constraint({:?}, {:?}, {:?})",
            location, borrow_region, borrowed_place
        );
        while let Projection(box PlaceProjection { base, elem }) = borrowed_place {
            debug!("add_reborrow_constraint - iteration {:?}", borrowed_place);

            match *elem {
                ProjectionElem::Deref => {
                    let tcx = self.infcx.tcx;
                    let base_ty = base.ty(self.mir, tcx).to_ty(tcx);

                    debug!("add_reborrow_constraint - base_ty = {:?}", base_ty);
                    match base_ty.sty {
                        ty::TyRef(ref_region, ty::TypeAndMut { ty: _, mutbl }) => {
                            let span = self.mir.source_info(location).span;
                            self.regioncx.add_outlives(
                                span,
                                ref_region.to_region_vid(),
                                borrow_region.to_region_vid(),
                                location.successor_within_block(),
                            );

                            self.all_facts.outlives.push((
                                ref_region.to_region_vid(),
                                borrow_region.to_region_vid(),
                                self.location_table.mid_index(location),
                            ));

                            match mutbl {
                                hir::Mutability::MutImmutable => {
                                    // Immutable reference. We don't need the base
                                    // to be valid for the entire lifetime of
                                    // the borrow.
                                    break;
                                }
                                hir::Mutability::MutMutable => {
                                    // Mutable reference. We *do* need the base
                                    // to be valid, because after the base becomes
                                    // invalid, someone else can use our mutable deref.

                                    // This is in order to make the following function
                                    // illegal:
                                    // ```
                                    // fn unsafe_deref<'a, 'b>(x: &'a &'b mut T) -> &'b mut T {
                                    //     &mut *x
                                    // }
                                    // ```
                                    //
                                    // As otherwise you could clone `&mut T` using the
                                    // following function:
                                    // ```
                                    // fn bad(x: &mut T) -> (&mut T, &mut T) {
                                    //     let my_clone = unsafe_deref(&'a x);
                                    //     ENDREGION 'a;
                                    //     (my_clone, x)
                                    // }
                                    // ```
                                }
                            }
                        }
                        ty::TyRawPtr(..) => {
                            // deref of raw pointer, guaranteed to be valid
                            break;
                        }
                        ty::TyAdt(def, _) if def.is_box() => {
                            // deref of `Box`, need the base to be valid - propagate
                        }
                        _ => bug!("unexpected deref ty {:?} in {:?}", base_ty, borrowed_place),
                    }
                }
                ProjectionElem::Field(..)
                | ProjectionElem::Downcast(..)
                | ProjectionElem::Index(..)
                | ProjectionElem::ConstantIndex { .. }
                | ProjectionElem::Subslice { .. } => {
                    // other field access
                }
            }

            // The "propagate" case. We need to check that our base is valid
            // for the borrow's lifetime.
            borrowed_place = base;
        }
    }
}
