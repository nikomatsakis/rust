// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::nll::region_infer::borrows_in_scope::AllFacts;
use borrow_check::nll::region_infer::values::RegionValueElements;
use borrow_check::nll::region_infer::RegionInferenceContext;
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
        mir: &Mir<'tcx>,
        _mir_def_id: DefId,
    ) -> Self {
        let mut collector = FactCollector {
            regioncx,
            elements: &regioncx.elements,
            all_facts: AllFacts::default(),
        };
        collector.visit_mir(mir);
        collector.liveness();
        collector.outlives();
        collector.all_facts
    }

    crate fn write_to_dir(&self, dir: impl AsRef<Path>) -> Result<(), Box<dyn Error>> {
        let dir: &Path = dir.as_ref();
        fs::create_dir_all(dir)?;
        write_facts_to_path(&self.successor, dir.join("successor.facts"))?;
        write_facts_to_path(&self.outlives, dir.join("outlives.facts"))?;
        write_facts_to_path(&self.region_live_at, dir.join("region_live_at.facts"))?;
        Ok(())
    }
}

struct FactCollector<'cx, 'tcx: 'cx> {
    regioncx: &'cx RegionInferenceContext<'tcx>,
    all_facts: AllFacts,
    elements: &'cx RegionValueElements,
}

impl<'cx, 'tcx> FactCollector<'cx, 'tcx> {
    fn liveness(&mut self) {
        for region_vid in self.regioncx.definitions.indices() {
            for element_index in self.regioncx
                .liveness_constraints
                .element_indices_contained_in(region_vid)
            {
                self.all_facts
                    .region_live_at
                    .push((region_vid, element_index));
            }
        }
    }

    fn outlives(&mut self) {
        for constraint in &self.regioncx.constraints {
            self.all_facts.outlives.push((
                constraint.sup,
                constraint.sub,
                self.elements.index(constraint.point),
            ));
        }
    }
}

impl<'cx, 'tcx> Visitor<'tcx> for FactCollector<'cx, 'tcx> {
    fn visit_statement(
        &mut self,
        block: BasicBlock,
        statement: &Statement<'tcx>,
        location: Location,
    ) {
        self.all_facts.successor.push((
            self.elements.index(location),
            self.elements.index(location.successor_within_block()),
        ));

        self.super_statement(block, statement, location);
    }

    fn visit_terminator(
        &mut self,
        block: BasicBlock,
        terminator: &Terminator<'tcx>,
        location: Location,
    ) {
        let location_element_index = self.elements.index(location);
        let successors = terminator.successors();
        if !successors.is_empty() {
            for successor in successors.iter() {
                self.all_facts.successor.push((
                    location_element_index,
                    self.elements.index(successor.start_location()),
                ));
            }
        } else {
            for universal_region_index in self.elements.all_universal_region_indices() {
                self.all_facts.successor
                    .push((location_element_index, universal_region_index));
            }
        }

        self.super_terminator(block, terminator, location);
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
