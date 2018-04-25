// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::borrow_set::BorrowRegionVid;
use borrow_check::location::{LocationIndex, LocationTable};
use rustc::mir::Local;
use rustc::ty::RegionVid;
use std::error::Error;
use std::fmt::Debug;
use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

/// The "facts" which are the basis of the NLL borrow analysis.
#[derive(Default)]
crate struct AllFacts {
    // For each `&'a T` rvalue at point P, include ('a, B, P).
    //
    // XXX Universal regions?
    crate borrow_region: Vec<(RegionVid, BorrowRegionVid, LocationIndex)>,

    // `cfg_edge(P,Q)` for each edge P -> Q in the control flow
    crate cfg_edge: Vec<(LocationIndex, LocationIndex)>,

    // `killed(B,P)` when some prefix of the path borrowed at B is assigned at point P
    crate killed: Vec<(BorrowRegionVid, LocationIndex)>,

    // `outlives(R1, R2, P)` when we require `R1@P: R2@P`
    crate outlives: Vec<(RegionVid, RegionVid, LocationIndex)>,

    // `use_live(X, P)` when the variable X is "use-live" on entry to P
    //
    // This could (should?) eventually be propagated by the timely dataflow code.
    crate use_live: Vec<(Local, LocationIndex)>,

    // `drop_live(X, P)` when the variable X is "drop-live" on entry to P
    //
    // This could (should?) eventually be propagated by the timely dataflow code.
    crate drop_live: Vec<(Local, LocationIndex)>,

    // `covariant_var_region(X, R)` when the type of X includes X in a contravariant position
    crate covariant_var_region: Vec<(Local, RegionVid)>,

    // `contravariant_var_region(X, R)` when the type of X includes X in a contravariant position
    crate contravariant_var_region: Vec<(Local, RegionVid)>,

    // `covariant_assign_region(P, R)` when P is an assignment and the type being assigned
    // contains region R in a covariant position.
    crate covariant_assign_region: Vec<(LocationIndex, RegionVid)>,

    // `contravariant_assign_region(P, R)` when P is an assignment and the type being assigned
    // contains region R in a contravariant position.
    crate contravariant_assign_region: Vec<(LocationIndex, RegionVid)>,

    // `drop_region(X, R)` when the region R must be live when X is dropped
    crate drop_region: Vec<(Local, RegionVid)>,
}

impl AllFacts {
    crate fn write_to_dir(
        &self,
        dir: impl AsRef<Path>,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>> {
        let dir: &Path = dir.as_ref();
        fs::create_dir_all(dir)?;
        let wr = FactWriter { location_table, dir };
        wr.write_facts_to_path(&self.borrow_region, "borrowRegion.facts")?;
        wr.write_facts_to_path(&self.cfg_edge, "cfgEdge.facts")?;
        wr.write_facts_to_path(&self.killed, "killed.facts")?;
        wr.write_facts_to_path(&self.outlives, "outlives.facts")?;
        wr.write_facts_to_path(&self.use_live, "useLive.facts")?;
        wr.write_facts_to_path(&self.drop_live, "dropLive.facts")?;
        wr.write_facts_to_path(
            &self.covariant_var_region,
            "covariantVarRegion.facts",
        )?;
        wr.write_facts_to_path(
            &self.contravariant_var_region,
            "contravariantVarRegion.facts",
        )?;
        wr.write_facts_to_path(
            &self.covariant_assign_region,
            "covariantAssignRegion.facts",
        )?;
        wr.write_facts_to_path(
            &self.contravariant_assign_region,
            "contravariantAssignRegion.facts",
        )?;
        wr.write_facts_to_path(&self.drop_region, "dropRegion.facts")?;
        Ok(())
    }
}

struct FactWriter<'w> {
    location_table: &'w LocationTable,
    dir: &'w Path,
}

impl<'w> FactWriter<'w> {
    fn write_facts_to_path<T>(
        &self,
        rows: &Vec<T>,
        file_name: &str,
    ) -> Result<(), Box<dyn Error>>
    where
        T: FactRow,
    {
        let file = &self.dir.join(file_name);
        let mut file = File::create(file)?;
        for row in rows {
            row.write(&mut file, self.location_table)?;
        }
        Ok(())
    }
}

trait FactRow {
    fn write(
        &self,
        out: &mut File,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>>;
}

impl<A, B> FactRow for (A, B)
where
    A: FactToString,
    B: FactToString,
{
    fn write(
        &self,
        out: &mut File,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>> {
        write_row(out, location_table, &[&self.0, &self.1])
    }
}

impl<A, B, C> FactRow for (A, B, C)
where
    A: FactToString,
    B: FactToString,
    C: FactToString,
{
    fn write(
        &self,
        out: &mut File,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>> {
        write_row(out, location_table, &[&self.0, &self.1, &self.2])
    }
}

impl<A, B, C, D> FactRow for (A, B, C, D)
where
    A: FactToString,
    B: FactToString,
    C: FactToString,
    D: FactToString,
{
    fn write(
        &self,
        out: &mut File,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>> {
        write_row(out, location_table, &[&self.0, &self.1, &self.2, &self.3])
    }
}

fn write_row(
    out: &mut dyn Write,
    location_table: &LocationTable,
    columns: &[&dyn FactToString],
) -> Result<(), Box<dyn Error>> {
    for (index, c) in columns.iter().enumerate() {
        let tail = if index == columns.len() - 1 {
            "\n"
        } else {
            "\t"
        };
        write!(out, "{:?}{}", c.to_string(location_table), tail)?;
    }
    Ok(())
}

trait FactToString {
    fn to_string(&self, location_table: &LocationTable) -> String;
}

impl<T: Debug> FactToString for T {
    default fn to_string(&self, _location_table: &LocationTable) -> String {
        format!("{:?}", self)
    }
}

impl FactToString for LocationIndex {
    fn to_string(&self, location_table: &LocationTable) -> String {
        format!("{:?}", location_table.to_location(*self))
    }
}
