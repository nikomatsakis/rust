// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::BorrowSet;
use borrow_check::nll::region_infer::RegionInferenceContext;
use borrow_check::nll::region_infer::borrows_in_scope::AllFacts;
use rustc::hir::def_id::DefId;
use rustc::mir::visit::Visitor;
use rustc::mir::{BasicBlock, Local, Location, Mir, Place, Rvalue, Statement, StatementKind,
                 Terminator};
use std::error::Error;
use std::fmt::Debug;
use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

impl AllFacts {
    crate fn produce<'cx, 'gcx, 'tcx>(
        regioncx: &RegionInferenceContext<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        mir: &Mir<'tcx>,
        _mir_def_id: DefId,
    ) -> Self {
        let mut dumper = FactCollector {
            regioncx,
            borrow_set,
            all_facts: AllFacts::default(),
        };
        dumper.visit_mir(mir);
        dumper.write_constraints();
        dumper.all_facts
    }

    crate fn write_to_dir(&self, dir: impl AsRef<Path>) -> Result<(), Box<dyn Error>> {
        let dir: &Path = dir.as_ref();
        fs::create_dir_all(dir)?;
        write_facts_to_path(&self.borrow_region, dir.join("borrowRegion.facts"))?;
        write_facts_to_path(&self.next_statement, dir.join("nextStatement.facts"))?;
        write_facts_to_path(&self.goto, dir.join("goto.facts"))?;
        write_facts_to_path(
            &self.region_live_on_entry,
            dir.join("regionLiveOnEntryToStatement.facts"),
        )?;
        write_facts_to_path(&self.killed, dir.join("killed.facts"))?;
        write_facts_to_path(&self.outlives, dir.join("outlives.facts"))?;
        Ok(())
    }
}

struct FactCollector<'cx, 'tcx: 'cx> {
    regioncx: &'cx RegionInferenceContext<'tcx>,
    borrow_set: &'cx BorrowSet<'tcx>,
    all_facts: AllFacts,
}

impl<'cx, 'tcx> Visitor<'tcx> for FactCollector<'cx, 'tcx> {
    fn visit_rvalue(&mut self, rvalue: &Rvalue<'tcx>, location: Location) {
        if let Rvalue::Ref(region, _bk, _place) = rvalue {
            if let Some(borrow_index) = self.borrow_set.location_map.get(&location) {
                let region_vid = self.regioncx.to_region_vid(region);
                self.all_facts
                    .borrow_region
                    .push((region_vid, *borrow_index, location));
            } else {
                // Some borrows don't get a borrow index -- these
                // correspond to cases where the borrow checker
                // doesn't have to do any work, because we can check
                // the full conditions up front. For example, a borrow
                // of a static, or of the referent from an unsafe
                // pointer. Just ignore those.
            }
        }

        self.super_rvalue(rvalue, location);
    }

    fn visit_statement(
        &mut self,
        block: BasicBlock,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.all_facts
            .next_statement
            .push((location, location.successor_within_block()));

        self.visit_location(location);

        match &statement.kind {
            StatementKind::Assign(lhs, _) => {
                if let Place::Local(local) = lhs {
                    self.kill_local(*local, location);
                }
            }

            StatementKind::StorageDead(local) => {
                self.kill_local(*local, location);
            }

            StatementKind::InlineAsm { outputs, asm, .. } => {
                for (output, kind) in outputs.iter().zip(&asm.outputs) {
                    if !kind.is_indirect && !kind.is_rw {
                        if let Place::Local(local) = output {
                            self.kill_local(*local, location);
                        }
                    }
                }
            }

            _ => {}
        }

        self.super_statement(block, statement, location);
    }

    fn visit_terminator(
        &mut self,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        for successor in terminator.successors().iter() {
            self.all_facts
                .goto
                .push((location, successor.start_location()));
        }

        self.visit_location(location);

        self.super_terminator(block, terminator, location);
    }
}

impl<'cx, 'tcx> FactCollector<'cx, 'tcx> {
    /// Record that a local is killed at a certain point. This will be
    /// combined later with the list of borrows to create a list of
    /// killed borrows at each point.
    fn kill_local(&mut self, local: Local, point: Location) {
        if let Some(borrows) = self.borrow_set.local_map.get(&local) {
            for borrow in borrows {
                self.all_facts.killed.push((*borrow, point));
            }
        }
    }

    fn write_constraints(&mut self) {
        for (source_point, sup, sub, effect_point) in self.regioncx.outlives_constraints_iter() {
            self.all_facts
                .outlives
                .push((source_point, sup, sub, effect_point));
        }
    }

    fn visit_location(&mut self, location: Location) {
        for region in self.regioncx.live_regions_at_point(location) {
            self.all_facts.region_live_on_entry.push((region, location));
        }
    }
}

fn write_facts_to_path<T>(rows: &Vec<T>, file: impl AsRef<Path>) -> Result<(), Box<dyn Error>>
where
    T: FactRow,
{
    let file: &Path = file.as_ref();
    let mut file = File::create(file)?;
    for row in rows {
        row.write(&mut file)?;
    }
    Ok(())
}

trait FactRow {
    fn write(&self, out: &mut File) -> Result<(), Box<dyn Error>>;
}

impl<A, B> FactRow for (A, B)
where
    A: Debug,
    B: Debug,
{
    fn write(&self, out: &mut File) -> Result<(), Box<dyn Error>> {
        write_row(out, &[&self.0, &self.1])
    }
}

impl<A, B, C> FactRow for (A, B, C)
where
    A: Debug,
    B: Debug,
    C: Debug,
{
    fn write(&self, out: &mut File) -> Result<(), Box<dyn Error>> {
        write_row(out, &[&self.0, &self.1, &self.2])
    }
}

impl<A, B, C, D> FactRow for (A, B, C, D)
where
    A: Debug,
    B: Debug,
    C: Debug,
    D: Debug,
{
    fn write(&self, out: &mut File) -> Result<(), Box<dyn Error>> {
        write_row(out, &[&self.0, &self.1, &self.2, &self.3])
    }
}

fn write_row(out: &mut dyn Write, columns: &[&Debug]) -> Result<(), Box<dyn Error>> {
    for (index, c) in columns.iter().enumerate() {
        let tail = if index == columns.len() - 1 {
            "\n"
        } else {
            "\t"
        };
        write!(out, "\"{:?}\"{}", c, tail)?;
    }
    Ok(())
}
