// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use std::kinds::marker;

struct Foo<T,U>(T, marker::CovariantType<U>);

fn main() {
    match Foo(1.1, marker::CovariantType) {
        1 => {}
    //~^ ERROR expected `Foo<_, _>`, found `_`
    }

}
