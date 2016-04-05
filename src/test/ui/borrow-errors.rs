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

fn one_simple() {
    let mut vec = vec!["hi"];
    let data = &vec[22];
    // do some stuff
    // do some more stuff
    // do even more stuff
    vec.push("ho");
}

fn two_loop() {
    let mut vec = vec!["hi"];
    let mut data;
    loop {
        data = &mut vec[3];
    }
}

fn three_closure() {
    let mut vec = vec!["hi"];
    let append = |e| vec.push(e);
    let data = &vec[3];
}

fn four_closure() {
    let mut vec = vec!["hi"];
    let append = |e| {
        vec.push(e)
    };
    let data = &vec[3];
}

fn five_closure() {
    let mut vec = vec!["hi"];
    let data = &vec[3];
    let append = |e| vec.push(e);
}

fn six_closure() {
    let mut vec = vec!["hi"];
    let data = &vec[3];
    let append = |e| {
        vec.push(e)
    };
}

fn closure_borrow_unique() {
    let mut vec = vec!["hi"];
    let vec = &mut vec;
    let data = &vec[3];
    let append = |e| {
        vec.push(e)
    };
}

fn closure_unique_borrow() {
    let mut vec = vec!["hi"];
    let vec = &mut vec;
    let append = |e| {
        vec.push(e)
    };
    let data = &vec[3];
}

fn closure_unique_unique() {
    let mut vec = vec!["hi"];
    let vec = &mut vec;
    let append = |e| {
        vec.push(e)
    };
    let append = |e| {
        vec.push(e)
    };
}

fn mut_mut() {
    let mut vec = vec!["hi"];
    let vec1 = &mut vec;
    let vec2 = &mut vec;
}

fn ref_mut_ref_mut() {
    let mut vec = vec!["hi"];
    let ref mut vec1 = vec;
    let ref mut vec2 = vec;
}

fn main() { }
