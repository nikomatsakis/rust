// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(default_type_params)]

use std::kinds::marker;

struct Foo<A, B, C = (A, B)>(
    marker::InvariantType<(A,B,C)>);

impl<A, B, C = (A, B)> Foo<A, B, C> {
    fn new() -> Foo<A, B, C> {Foo(marker::InvariantType)}
}

fn main() {
    Foo::<int>::new();
    //~^ ERROR too few type parameters provided
}
