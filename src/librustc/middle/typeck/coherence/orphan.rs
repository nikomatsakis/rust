// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

/*!
 * Orphan checker: every impl either implements a trait defined in this
 * crate or pertains to a type defined in this crate.
 */

use middle::traits;
use middle::ty;
use syntax::ast::{Crate};
use syntax::ast::{Item, ItemImpl};
use syntax::ast;
use syntax::ast_util;
use syntax::visit;
use util::ppaux::Repr;

pub fn check(tcx: &ty::ctxt, krate: &Crate) {
    let mut orphan = OrphanChecker { tcx: tcx };
    visit::walk_crate(&mut orphan, krate, ());
}

struct OrphanChecker<'cx> {
    tcx: &'cx ty::ctxt
}

impl<'cx> visit::Visitor<()> for OrphanChecker<'cx> {
    fn visit_item(&mut self, item: &ast::Item, _: ()) {
        let def_id = ast_util::local_def(item.id);
        match item.node {
            ast::ItemImpl(_, None, _, _) => {
                // "Inherent" impl
                debug!("coherence2::orphan check: inherent impl {}", item.repr(self.tcx));
                // WARN: Error number
                if traits::is_orphan_impl(self.tcx, def_id) {
                    self.tcx.sess.span_err(
                        item.span,
                        "no base type found for inherent implementation; \
                         implement a trait or new type instead");
                }
            }
            ast::ItemImpl(_, Some(_), _, _) => {
                // "Trait" impl
                debug!("coherence2::orphan check: trait impl {}", item.repr(self.tcx));
                if traits::is_orphan_impl(self.tcx, def_id) {
                    // WARN: Error number
                    self.tcx.sess.span_err(
                        item.span,
                        "cannot provide an extension implementation \
                         where both trait and type are not defined in this crate");
                }
            }
            _ => {
                // Not an impl
            }
        }

        visit::walk_item(self, item, ());
    }
}
