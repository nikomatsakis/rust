// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use borrow_check::nll::AllFacts;
use std::error::Error;
use std::fmt::Debug;
use std::fs::{self, File};
use std::io::Write;
use std::path::Path;

impl AllFacts {
    crate fn write_to_dir(&self, dir: impl AsRef<Path>) -> Result<(), Box<dyn Error>> {
        let dir: &Path = dir.as_ref();
        fs::create_dir_all(dir)?;
        write_facts_to_path(&self.borrow_region, dir.join("borrowRegion.facts"))?;
        write_facts_to_path(&self.cfg_edge, dir.join("cfgEdge.facts"))?;
        write_facts_to_path(&self.killed, dir.join("killed.facts"))?;
        write_facts_to_path(&self.outlives, dir.join("outlives.facts"))?;
        write_facts_to_path(&self.use_live, dir.join("useLive.facts"))?;
        write_facts_to_path(&self.drop_live, dir.join("dropLive.facts"))?;
        write_facts_to_path(&self.covariant_region, dir.join("covariantRegion.facts"))?;
        write_facts_to_path(&self.contravariant_region, dir.join("contravariantRegion.facts"))?;
        write_facts_to_path(&self.drop_region, dir.join("dropRegion.facts"))?;
        Ok(())
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
