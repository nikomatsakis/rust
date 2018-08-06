// Copyright 2012-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::{BorrowData, BorrowSet};
use borrow_check::place_ext::PlaceExt;

use rustc;
use rustc::hir::def_id::DefId;
use rustc::middle::region;
use rustc::mir::{self, Location, Mir, Place};
use rustc::ty::TyCtxt;
use rustc::ty::{RegionKind, RegionVid};

use rustc_data_structures::bitslice::{BitwiseOperator, Word};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use rustc_data_structures::indexed_set::IdxSet;
use rustc_data_structures::indexed_vec::IndexVec;
use rustc_data_structures::sync::Lrc;

use borrow_check::nll::region_infer::RegionInferenceContext;
use borrow_check::nll::ToRegionVid;
pub use dataflow::indexes::BorrowIndex;
use dataflow::{BitDenotation, BlockSets, InitialFlow};

use std::rc::Rc;

/// `Borrows` stores the data used in the analyses that track the flow
/// of borrows.
///
/// It uniquely identifies every borrow (`Rvalue::Ref`) by a
/// `BorrowIndex`, and maps each such index to a `BorrowData`
/// describing the borrow. These indexes are used for representing the
/// borrows in compact bitvectors.
pub struct Borrows<'a, 'gcx: 'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    scope_tree: Lrc<region::ScopeTree>,

    borrow_set: Rc<BorrowSet<'tcx>>,
    borrows_out_of_scope_at_location: FxHashMap<Location, Vec<BorrowIndex>>,

    /// NLL region inference context with which NLL queries should be resolved
    _nonlexical_regioncx: Rc<RegionInferenceContext<'tcx>>,
}

fn precompute_borrows_out_of_scope<'tcx>(
    mir: &Mir<'tcx>,
    regioncx: &Rc<RegionInferenceContext<'tcx>>,
    borrows_out_of_scope_at_location: &mut FxHashMap<Location, Vec<BorrowIndex>>,
    borrow_index: BorrowIndex,
    borrow_region: RegionVid,
    start_location: Location,
) {
    // The first block is strange, in that we start traversing it not
    // from the start location but from mid-way through the block.
    let Location {
        block: start_block,
        statement_index: start_statement_index,
    } = start_location;
    let start_bb_data = &mir[start_block];
    for si in start_statement_index..start_bb_data.statements.len() {
        let location = Location {
            block: start_block,
            statement_index: si,
        };

        // If region does not contain a point at the location, then
        // add to list and skip successor locations.
        if !regioncx.region_contains(borrow_region, location) {
            debug!("borrow {:?} gets killed at {:?}", borrow_index, location);
            borrows_out_of_scope_at_location
                .entry(location)
                .or_insert(vec![])
                .push(borrow_index);
            return;
        }
    }

    // If region does not contain a point at the location, then
    // add to list and skip successor locations.
    let start_block_end_location = mir.terminator_loc(start_block);
    if !regioncx.region_contains(borrow_region, start_block_end_location) {
        debug!("borrow {:?} gets killed at {:?}", borrow_index, start_block_end_location);
        borrows_out_of_scope_at_location
            .entry(start_block_end_location)
            .or_insert(vec![])
            .push(borrow_index);
        return;
    }

    // Keep track of places we've locations to check and locations
    // that we have checked.
    let mut visited = FxHashSet();

    let mut stack: Vec<_> = start_bb_data
        .terminator()
        .successors()
        .cloned()
        .filter(|&block| visited.insert(block))
        .collect();

    debug!(
        "borrow {:?} has region {:?} with value {:?}",
        borrow_index,
        borrow_region,
        regioncx.region_value_str(borrow_region),
    );

    debug!("borrow {:?} starts at {:?}", borrow_index, start_location);
    'l: while let Some(block) = stack.pop() {
        let bb_data = &mir[block];

        let end_statement_index = if block == start_block {
            start_statement_index
        } else {
            bb_data.statements.len()
        };

        for si in 0..end_statement_index {
            let location = Location {
                block,
                statement_index: si,
            };

            // If region does not contain a point at the location, then
            // add to list and skip successor locations.
            if !regioncx.region_contains(borrow_region, location) {
                debug!("borrow {:?} gets killed at {:?}", borrow_index, location);
                borrows_out_of_scope_at_location
                    .entry(location)
                    .or_insert(vec![])
                    .push(borrow_index);
                continue 'l;
            }
        }

        // Add successor locations to visit, if not visited before.
        if block != start_block {
            // If region does not contain a point at the location, then
            // add to list and skip successor locations.
            let block_end_location = mir.terminator_loc(block);
            if !regioncx.region_contains(borrow_region, block_end_location) {
                debug!("borrow {:?} gets killed at {:?}", borrow_index, block_end_location);
                borrows_out_of_scope_at_location
                    .entry(block_end_location)
                    .or_insert(vec![])
                    .push(borrow_index);
                continue 'l;
            }

            stack.extend(
                bb_data
                    .terminator()
                    .successors()
                    .cloned()
                    .filter(|&block| visited.insert(block)),
            );
        }
    }
}

impl<'a, 'gcx, 'tcx> Borrows<'a, 'gcx, 'tcx> {
    crate fn new(
        tcx: TyCtxt<'a, 'gcx, 'tcx>,
        mir: &'a Mir<'tcx>,
        nonlexical_regioncx: Rc<RegionInferenceContext<'tcx>>,
        def_id: DefId,
        borrow_set: &Rc<BorrowSet<'tcx>>,
    ) -> Self {
        let scope_tree = tcx.region_scope_tree(def_id);

        let mut borrows_out_of_scope_at_location = FxHashMap();
        for (borrow_index, borrow_data) in borrow_set.borrows.iter_enumerated() {
            let borrow_region = borrow_data.region.to_region_vid();
            let location = borrow_set.borrows[borrow_index].reserve_location;

            precompute_borrows_out_of_scope(
                mir,
                &nonlexical_regioncx,
                &mut borrows_out_of_scope_at_location,
                borrow_index,
                borrow_region,
                location,
            );
        }

        Borrows {
            tcx: tcx,
            mir: mir,
            borrow_set: borrow_set.clone(),
            borrows_out_of_scope_at_location,
            scope_tree,
            _nonlexical_regioncx: nonlexical_regioncx,
        }
    }

    crate fn borrows(&self) -> &IndexVec<BorrowIndex, BorrowData<'tcx>> {
        &self.borrow_set.borrows
    }
    pub fn scope_tree(&self) -> &Lrc<region::ScopeTree> {
        &self.scope_tree
    }

    pub fn location(&self, idx: BorrowIndex) -> &Location {
        &self.borrow_set.borrows[idx].reserve_location
    }

    /// Add all borrows to the kill set, if those borrows are out of scope at `location`.
    /// That means either they went out of either a nonlexical scope, if we care about those
    /// at the moment, or the location represents a lexical EndRegion
    fn kill_loans_out_of_scope_at_location(
        &self,
        sets: &mut BlockSets<BorrowIndex>,
        location: Location,
    ) {
        // NOTE: The state associated with a given `location`
        // reflects the dataflow on entry to the statement.
        // Iterate over each of the borrows that we've precomputed
        // to have went out of scope at this location and kill them.
        //
        // We are careful always to call this function *before* we
        // set up the gen-bits for the statement or
        // termanator. That way, if the effect of the statement or
        // terminator *does* introduce a new loan of the same
        // region, then setting that gen-bit will override any
        // potential kill introduced here.
        if let Some(indices) = self.borrows_out_of_scope_at_location.get(&location) {
            for index in indices {
                sets.kill(&index);
            }
        }
    }

    fn kill_borrows_on_local(&self, sets: &mut BlockSets<BorrowIndex>, local: &rustc::mir::Local) {
        if let Some(borrow_indexes) = self.borrow_set.local_map.get(local) {
            sets.kill_all(borrow_indexes);
        }
    }
}

impl<'a, 'gcx, 'tcx> BitDenotation for Borrows<'a, 'gcx, 'tcx> {
    type Idx = BorrowIndex;
    fn name() -> &'static str {
        "borrows"
    }
    fn bits_per_block(&self) -> usize {
        self.borrow_set.borrows.len() * 2
    }

    fn start_block_effect(&self, _entry_set: &mut IdxSet<BorrowIndex>) {
        // no borrows of code region_scopes have been taken prior to
        // function execution, so this method has no effect on
        // `_sets`.
    }

    fn before_statement_effect(&self, sets: &mut BlockSets<BorrowIndex>, location: Location) {
        debug!(
            "Borrows::before_statement_effect sets: {:?} location: {:?}",
            sets, location
        );
        self.kill_loans_out_of_scope_at_location(sets, location);
    }

    fn statement_effect(&self, sets: &mut BlockSets<BorrowIndex>, location: Location) {
        debug!(
            "Borrows::statement_effect sets: {:?} location: {:?}",
            sets, location
        );

        let block = &self
            .mir
            .basic_blocks()
            .get(location.block)
            .unwrap_or_else(|| {
                panic!("could not find block at location {:?}", location);
            });
        let stmt = block
            .statements
            .get(location.statement_index)
            .unwrap_or_else(|| {
                panic!("could not find statement at location {:?}");
            });

        match stmt.kind {
            mir::StatementKind::EndRegion(_) => {}

            mir::StatementKind::Assign(ref lhs, ref rhs) => {
                // Make sure there are no remaining borrows for variables
                // that are assigned over.
                if let Place::Local(ref local) = *lhs {
                    // FIXME: Handle the case in which we're assigning over
                    // a projection (`foo.bar`).
                    self.kill_borrows_on_local(sets, local);
                }

                // NOTE: if/when the Assign case is revised to inspect
                // the assigned_place here, make sure to also
                // re-consider the current implementations of the
                // propagate_call_return method.

                if let mir::Rvalue::Ref(region, _, ref place) = *rhs {
                    if place.is_unsafe_place(self.tcx, self.mir) {
                        return;
                    }
                    let index = self
                        .borrow_set
                        .location_map
                        .get(&location)
                        .unwrap_or_else(|| {
                            panic!("could not find BorrowIndex for location {:?}", location);
                        });

                    if let RegionKind::ReEmpty = region {
                        // If the borrowed value dies before the borrow is used, the region for
                        // the borrow can be empty. Don't track the borrow in that case.
                        debug!(
                            "Borrows::statement_effect_on_borrows \
                             location: {:?} stmt: {:?} has empty region, killing {:?}",
                            location, stmt.kind, index
                        );
                        sets.kill(&index);
                        return;
                    } else {
                        debug!(
                            "Borrows::statement_effect_on_borrows location: {:?} stmt: {:?}",
                            location, stmt.kind
                        );
                    }

                    assert!(
                        self.borrow_set
                            .region_map
                            .get(region)
                            .unwrap_or_else(|| {
                                panic!("could not find BorrowIndexs for region {:?}", region);
                            }).contains(&index)
                    );
                    sets.gen(&index);
                }
            }

            mir::StatementKind::StorageDead(local) => {
                // Make sure there are no remaining borrows for locals that
                // are gone out of scope.
                self.kill_borrows_on_local(sets, &local)
            }

            mir::StatementKind::InlineAsm {
                ref outputs,
                ref asm,
                ..
            } => {
                for (output, kind) in outputs.iter().zip(&asm.outputs) {
                    if !kind.is_indirect && !kind.is_rw {
                        // Make sure there are no remaining borrows for direct
                        // output variables.
                        if let Place::Local(ref local) = *output {
                            // FIXME: Handle the case in which we're assigning over
                            // a projection (`foo.bar`).
                            self.kill_borrows_on_local(sets, local);
                        }
                    }
                }
            }

            mir::StatementKind::ReadForMatch(..)
            | mir::StatementKind::SetDiscriminant { .. }
            | mir::StatementKind::StorageLive(..)
            | mir::StatementKind::Validate(..)
            | mir::StatementKind::UserAssertTy(..)
            | mir::StatementKind::Nop => {}
        }
    }

    fn before_terminator_effect(&self, sets: &mut BlockSets<BorrowIndex>, location: Location) {
        debug!(
            "Borrows::before_terminator_effect sets: {:?} location: {:?}",
            sets, location
        );
        self.kill_loans_out_of_scope_at_location(sets, location);
    }

    fn terminator_effect(&self, _sets: &mut BlockSets<BorrowIndex>, _location: Location) {}

    fn propagate_call_return(
        &self,
        _in_out: &mut IdxSet<BorrowIndex>,
        _call_bb: mir::BasicBlock,
        _dest_bb: mir::BasicBlock,
        _dest_place: &mir::Place,
    ) {
        // there are no effects on borrows from method call return...
        //
        // ... but if overwriting a place can affect flow state, then
        // latter is not true; see NOTE on Assign case in
        // statement_effect_on_borrows.
    }
}

impl<'a, 'gcx, 'tcx> BitwiseOperator for Borrows<'a, 'gcx, 'tcx> {
    #[inline]
    fn join(&self, pred1: Word, pred2: Word) -> Word {
        pred1 | pred2 // union effects of preds when computing reservations
    }
}

impl<'a, 'gcx, 'tcx> InitialFlow for Borrows<'a, 'gcx, 'tcx> {
    #[inline]
    fn bottom_value() -> bool {
        false // bottom = nothing is reserved or activated yet
    }
}
