// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use front::map::Map;
use middle::def_id::DefId;
use rustc_front::hir;
use rustc_front::intravisit;

use super::defs::{self, DefsVisitor};

#[allow(unused_variables)]
pub trait ContentsVisitor<'tcx>: intravisit::Visitor<'tcx> {
    fn should_visit_item(&mut self, def_id: DefId) -> bool {
        true
    }

    fn visit_item(&mut self, i: &'tcx hir::Item) {
        intravisit::walk_item(self, i)
    }
}

pub fn execute<'tcx, D>(map: &Map<'tcx>, delegate: &mut D)
    where D: ContentsVisitor<'tcx>
{
    defs::execute(map, &mut ContentsAdapter { delegate: delegate });
}

struct ContentsAdapter<'a, D:'a> {
    delegate: &'a mut D,
}

// The poor man's inheritance: ContentsVisitor is basically the same
// as DefsVisitor, but with different default behavior.
impl<'a, 'tcx, D> DefsVisitor<'tcx> for ContentsAdapter<'a, D>
    where D: ContentsVisitor<'tcx>
{
    fn should_visit_item(&mut self, def_id: DefId) -> bool {
        self.delegate.should_visit_item(def_id)
    }

    fn visit_item(&mut self, item: &'tcx hir::Item) {
        self.delegate.visit_item(item)
    }
}


