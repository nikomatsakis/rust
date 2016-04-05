// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(warnings)]

use std::mem;

fn one_simple() {
    let v = vec!["hi"];
    loop {
        mem::drop(v);
    }
}

fn pat_binding_in_loop() {
    let v = vec!["hi"];
    loop {
        match v {
            w => { }
        }
    }
}

fn already_moved() {
    let v = vec!["hi"];
    mem::drop(v);
    mem::drop(v);
}

fn pat_binding_twice() {
    let v = vec!["hi"];
    match v {
        w => { }
    }
    match v {
        w => { }
    }
}

fn closure_twice() {
    let v = vec!["hi"];
    let c1 = || mem::drop(v);
    let c2 = || mem::drop(v);
}

fn main() { }
