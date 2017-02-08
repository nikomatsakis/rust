// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test that we are able to skip borrowck if nothing has changed.  The
// `rustc_no_borrowck` attribute will error out in the case that we
// actually run borrowck.

// revisions:rpass1 rpass2
// compile-flags: -Z query-dep-graph

#![feature(rustc_attrs)]

#[cfg_attr(rpass2, rustc_no_borrowck)]
pub fn blah() {
    let mut v = vec![];
    v.push(22);
}

pub fn main() { }
