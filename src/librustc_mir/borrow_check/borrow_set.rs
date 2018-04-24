// Copyright 2012-2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::nll::ToRegionVid;
use borrow_check::place_ext::PlaceExt;
use dataflow::indexes::BorrowIndex;
use rustc::mir::traversal;
use rustc::mir::visit::{PlaceContext, Visitor};
use rustc::mir::{self, Location, Mir, Place};
use rustc::ty::{Region, RegionVid, TyCtxt};
use rustc::util::nodemap::{FxHashMap, FxHashSet};
use rustc_data_structures::indexed_vec::IndexVec;
use std::fmt;
use std::hash::Hash;
use std::ops::Index;

crate struct BorrowSet<'tcx> {
    /// The fundamental map relating bitvector indexes to the borrows
    /// in the MIR.
    crate borrows: IndexVec<BorrowIndex, BorrowData<'tcx>>,

    /// Locations which activate borrows.
    /// NOTE: A given location may activate more than one borrow in the future
    /// when more general two-phase borrow support is introduced, but for now we
    /// only need to store one borrow index
    crate activation_map: FxHashMap<Location, Vec<BorrowIndex>>,

    /// Every borrow has a region; this maps each such regions back to
    /// its borrow-indexes.
    crate region_map: FxHashMap<BorrowRegionVid, BorrowIndex>,

    /// Map from local to all the borrows on that local
    crate local_map: FxHashMap<mir::Local, FxHashSet<BorrowIndex>>,
}

/// For each `foo = &'x bar` rvalue in the MIR, there is a region
/// associated with the borrow (`'x`, here). Moreover, after NLL has
/// rewritten the regions, this `'x` is always a region variable and
/// always unique (i.e., appears nowhere else in the MIR). In the
/// datalog, we use that unique region to describe the borrow, similar
/// to the `BorrowIndex` -- the reason we use the region and not the
/// `BorrowIndex` is so that we can also use it to represent named
/// lifetimes.
#[derive(Abomonation, Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct BorrowRegionVid {
    pub(crate) region_vid: RegionVid,
}

impl<'tcx> Index<BorrowIndex> for BorrowSet<'tcx> {
    type Output = BorrowData<'tcx>;

    fn index(&self, index: BorrowIndex) -> &BorrowData<'tcx> {
        &self.borrows[index]
    }
}

impl<'tcx> Index<BorrowRegionVid> for BorrowSet<'tcx> {
    type Output = BorrowData<'tcx>;

    fn index(&self, v: BorrowRegionVid) -> &BorrowData<'tcx> {
        let index = self.region_map[&v];
        &self[index]
    }
}

#[derive(Debug)]
crate struct BorrowData<'tcx> {
    /// Location where the borrow reservation starts.
    /// In many cases, this will be equal to the activation location but not always.
    crate reserve_location: Location,
    /// Location where the borrow is activated. None if this is not a
    /// 2-phase borrow.
    crate activation_location: Option<Location>,
    /// What kind of borrow this is
    crate kind: mir::BorrowKind,
    /// The unique region vid that identifies this borrow
    crate borrow_region_vid: BorrowRegionVid,
    /// The region for which this borrow is live
    crate region: Region<'tcx>,
    /// Place from which we are borrowing
    crate borrowed_place: mir::Place<'tcx>,
    /// Place to which the borrow was stored
    crate assigned_place: mir::Place<'tcx>,
}

impl<'tcx> fmt::Display for BorrowData<'tcx> {
    fn fmt(&self, w: &mut fmt::Formatter) -> fmt::Result {
        let kind = match self.kind {
            mir::BorrowKind::Shared => "",
            mir::BorrowKind::Unique => "uniq ",
            mir::BorrowKind::Mut { .. } => "mut ",
        };
        let region = format!("{}", self.region);
        let region = if region.len() > 0 {
            format!("{} ", region)
        } else {
            region
        };
        write!(w, "&{}{}{:?}", region, kind, self.borrowed_place)
    }
}

impl<'tcx> BorrowSet<'tcx> {
    pub fn build(tcx: TyCtxt<'_, '_, 'tcx>, mir: &Mir<'tcx>) -> Self {
        let mut visitor = GatherBorrows {
            tcx,
            mir,
            idx_vec: IndexVec::new(),
            activation_map: FxHashMap(),
            region_map: FxHashMap(),
            local_map: FxHashMap(),
            pending_activations: FxHashMap(),
        };

        for (block, block_data) in traversal::preorder(mir) {
            visitor.visit_basic_block_data(block, block_data);
        }

        // Double check: We should have found an activation for every pending
        // activation.
        assert_eq!(
            visitor
                .pending_activations
                .iter()
                .find(|&(_local, &borrow_index)| visitor.idx_vec[borrow_index]
                    .activation_location
                    .is_none()),
            None,
            "never found an activation for this borrow!",
        );

        BorrowSet {
            borrows: visitor.idx_vec,
            activation_map: visitor.activation_map,
            region_map: visitor.region_map,
            local_map: visitor.local_map,
        }
    }

    crate fn activations_at_location(&self, location: Location) -> &[BorrowIndex] {
        self.activation_map
            .get(&location)
            .map(|activations| &activations[..])
            .unwrap_or(&[])
    }
}

struct GatherBorrows<'a, 'gcx: 'tcx, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'gcx, 'tcx>,
    mir: &'a Mir<'tcx>,
    idx_vec: IndexVec<BorrowIndex, BorrowData<'tcx>>,
    activation_map: FxHashMap<Location, Vec<BorrowIndex>>,
    region_map: FxHashMap<BorrowRegionVid, BorrowIndex>,
    local_map: FxHashMap<mir::Local, FxHashSet<BorrowIndex>>,

    /// When we encounter a 2-phase borrow statement, it will always
    /// be assigning into a temporary TEMP:
    ///
    ///    TEMP = &foo
    ///
    /// We add TEMP into this map with `b`, where `b` is the index of
    /// the borrow. When we find a later use of this activation, we
    /// remove from the map (and add to the "tombstone" set below).
    pending_activations: FxHashMap<mir::Local, BorrowIndex>,
}

impl<'a, 'gcx, 'tcx> Visitor<'tcx> for GatherBorrows<'a, 'gcx, 'tcx> {
    fn visit_assign(
        &mut self,
        block: mir::BasicBlock,
        assigned_place: &mir::Place<'tcx>,
        rvalue: &mir::Rvalue<'tcx>,
        location: mir::Location,
    ) {
        if let mir::Rvalue::Ref(region, kind, ref borrowed_place) = *rvalue {
            if borrowed_place.is_unsafe_place(self.tcx, self.mir) {
                return;
            }

            let borrow_region_vid = BorrowRegionVid { region_vid: region.to_region_vid() };
            let borrow_index = self.idx_vec.push(BorrowData {
                kind,
                region,
                borrow_region_vid,
                reserve_location: location,
                activation_location: None,
                borrowed_place: borrowed_place.clone(),
                assigned_place: assigned_place.clone(),
            });

            self.insert_as_pending_if_two_phase(location, &assigned_place, region, kind, borrow_index);

            let old_value = self.region_map.insert(borrow_region_vid, borrow_index);
            assert!(old_value.is_none());

            if let Some(local) = borrowed_place.root_local() {
                insert(&mut self.local_map, &local, borrow_index);
            }
        }

        return self.super_assign(block, assigned_place, rvalue, location);

        fn insert<'a, K, V>(map: &'a mut FxHashMap<K, FxHashSet<V>>, k: &K, v: V)
        where
            K: Clone + Eq + Hash,
            V: Eq + Hash,
        {
            map.entry(k.clone()).or_insert(FxHashSet()).insert(v);
        }
    }

    fn visit_place(
        &mut self,
        place: &mir::Place<'tcx>,
        context: PlaceContext<'tcx>,
        location: Location,
    ) {
        self.super_place(place, context, location);

        // We found a use of some temporary TEMP...
        if let Place::Local(temp) = place {
            // ... check whether we (earlier) saw a 2-phase borrow like
            //
            //     TMP = &mut place
            match self.pending_activations.get(temp) {
                Some(&borrow_index) => {
                    let borrow_data = &mut self.idx_vec[borrow_index];

                    // Watch out: the use of TMP in the borrow
                    // itself doesn't count as an
                    // activation. =)
                    if borrow_data.reserve_location == location && context == PlaceContext::Store {
                        return;
                    }

                    if let Some(other_activation) = borrow_data.activation_location {
                        span_bug!(
                            self.mir.source_info(location).span,
                            "found two activations for 2-phase borrow temporary {:?}: \
                             {:?} and {:?}",
                            temp,
                            location,
                            other_activation,
                        );
                    }

                    // Otherwise, this is the unique later use
                    // that we expect.
                    borrow_data.activation_location = Some(location);
                    self.activation_map
                        .entry(location)
                        .or_insert(Vec::new())
                        .push(borrow_index);
                }

                None => {}
            }
        }
    }

    fn visit_statement(
        &mut self,
        block: mir::BasicBlock,
        statement: &mir::Statement<'tcx>,
        location: Location,
    ) {
        return self.super_statement(block, statement, location);
    }
}

impl<'a, 'gcx, 'tcx> GatherBorrows<'a, 'gcx, 'tcx> {
    /// Returns true if the borrow represented by `kind` is
    /// allowed to be split into separate Reservation and
    /// Activation phases.
    fn allow_two_phase_borrow(&self, kind: mir::BorrowKind) -> bool {
        self.tcx.two_phase_borrows()
            && (kind.allows_two_phase_borrow()
                || self.tcx.sess.opts.debugging_opts.two_phase_beyond_autoref)
    }

    /// If this is a two-phase borrow, then we will record it
    /// as "pending" until we find the activating use.
    fn insert_as_pending_if_two_phase(
        &mut self,
        start_location: Location,
        assigned_place: &mir::Place<'tcx>,
        region: Region<'tcx>,
        kind: mir::BorrowKind,
        borrow_index: BorrowIndex,
    ) {
        debug!(
            "Borrows::insert_as_pending_if_two_phase({:?}, {:?}, {:?}, {:?})",
            start_location, assigned_place, region, borrow_index,
        );

        if !self.allow_two_phase_borrow(kind) {
            debug!("  -> {:?}", start_location);
            return;
        }

        // When we encounter a 2-phase borrow statement, it will always
        // be assigning into a temporary TEMP:
        //
        //    TEMP = &foo
        //
        // so extract `temp`.
        let temp = if let &mir::Place::Local(temp) = assigned_place {
            temp
        } else {
            span_bug!(
                self.mir.source_info(start_location).span,
                "expected 2-phase borrow to assign to a local, not `{:?}`",
                assigned_place,
            );
        };

        // Insert `temp` into the list of pending activations. From
        // now on, we'll be on the lookout for a use of it. Note that
        // we are guaranteed that this use will come after the
        // assignment.
        let old_value = self.pending_activations.insert(temp, borrow_index);
        assert!(old_value.is_none());
    }
}
