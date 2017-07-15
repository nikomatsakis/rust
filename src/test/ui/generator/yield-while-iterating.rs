// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(generators, generator_trait)]

use std::ops::{State, Generator};
use std::cell::Cell;

fn yield_during_iter_owned_data(x: Vec<i32>) {
    // The generator owns `x`, so we error out when yielding with a
    // reference to it.  This winds up becoming a rather confusing
    // regionck error -- in particular, we would freeze with the
    // reference in scope, and it doesn't live long enough.
    let _b = move || {
        for p in &x { //~ ERROR
            yield();
        }
    };
}

fn yield_during_iter_borrowed_slice(x: &[i32]) {
    let _b = move || {
        for p in x {
            yield();
        }
    };
}

fn yield_during_iter_borrowed_slice_2() {
    let mut x = vec![22_i32];
    let _b = || {
        for p in &x {
            yield();
        }
    };
    println!("{:?}", x);
}

fn yield_during_iter_borrowed_slice_3() {
    // OK to take a mutable ref to `x` and yield
    // up pointers from it:
    let mut x = vec![22_i32];
    let mut b = || {
        for p in &mut x {
            yield p;
        }
    };
    b.resume();
}

fn yield_during_iter_borrowed_slice_4() {
    // ...but not OK to do that while reading
    // from `x` too
    let mut x = vec![22_i32];
    let mut b = || {
        for p in &mut x {
            yield p;
        }
    };
    println!("{}", x[0]); //~ ERROR
    b.resume();
}

fn main() { }
