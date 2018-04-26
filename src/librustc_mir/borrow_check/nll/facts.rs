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

    // universal_region(R) -- this is a "free region" within fn body
    crate universal_region: Vec<RegionVid>,

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

    // `use_region(X, R)` when the type of X includes R
    crate use_region: Vec<(Local, RegionVid)>,

    // `drop_region(X, R)` when the type of X will use R when dropped
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
        macro_rules! write_facts_to_path {
            ($wr:ident . write_facts_to_path($this:ident . [
                $($field:ident,)*
            ])) => {
                $(
                    $wr.write_facts_to_path(
                        &$this.$field,
                        &format!("{}.facts", stringify!($field))
                    )?;
                )*
            }
        }
        write_facts_to_path! {
            wr.write_facts_to_path(self.[
                borrow_region,
                universal_region,
                cfg_edge,
                killed,
                outlives,
                use_live,
                drop_live,
                use_region,
                drop_region,
            ])
        }
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

trait FactRow: Debug {
    fn write(
        &self,
        out: &mut File,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>>;

    fn to_string(&self, location_table: &LocationTable) -> String;
}

impl<A> FactRow for A
where
    A: Debug,
{
    default fn write(
        &self,
        out: &mut File,
        location_table: &LocationTable,
    ) -> Result<(), Box<dyn Error>> {
        write_row(out, location_table, &[self])
    }

    default fn to_string(&self, _location_table: &LocationTable) -> String {
        format!("{:?}", self)
    }
}

impl FactRow for LocationIndex {
    fn to_string(&self, location_table: &LocationTable) -> String {
        format!("{:?}", location_table.to_location(*self))
    }
}

impl<A, B> FactRow for (A, B)
where
    A: FactRow,
    B: FactRow,
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
    A: FactRow,
    B: FactRow,
    C: FactRow,
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
    A: FactRow,
    B: FactRow,
    C: FactRow,
    D: FactRow,
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
    columns: &[&dyn FactRow],
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
