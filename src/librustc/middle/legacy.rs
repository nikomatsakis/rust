// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use middle::ty;
use syntax::ast;
use syntax::attr::{self, AttrMetaMethods};

pub fn update_legacy<'tcx>(tcx: &ty::ctxt<'tcx>, krate: &ast::Crate) {
    for attr in &krate.attrs {
        if &attr.name()[..] != "legacy" {
            continue;
        }

        if attr.value_str().is_some() || attr.meta_item_list().is_none() {
            span_err!(tcx.sess, attr.span, E0398,
                      "legacy attribute should be used like `#[legacy(x, y, z)]`");
        }

        let meta_items = attr.meta_item_list().unwrap();
        let mut fully_used = true;
        for meta_item in meta_items {
            if meta_item.check_name("default_object_bounds") {
                if attr.value_str().is_some() {
                    span_err!(tcx.sess, attr.span, E0399,
                              "legacy attribute should be used \
                               like `#[legacy(default_object_bounds)]`");
                }

                tcx.legacy_default_object_bounds.set(true);
            } else {
                fully_used = false;
            }
        }

        if fully_used {
            attr::mark_used(attr);
        }
    }
}
