// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test that an appearance of `T` in fn args or in a trait object must
// still meet the outlives bounds. Since this is a new requirement,
// this is currently only a warning, not a hard error.

#![feature(rustc_attrs)]
#![allow(dead_code)]

trait Trait<T> { }

struct Foo<'a,T> {
    //~^ WARN E0309
    //~| WARN E0309
    f: &'a fn(T),
}

struct Bar<'a,T> {
    //~^ WARN E0309
    //~| WARN E0309
    f: &'a Trait<T>,
}

#[rustc_error]
fn main() { } //~ ERROR compilation successful

