// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(conservative_impl_trait)]

// Helper creating a fake borrow, captured by the impl Trait.
fn borrow<'a, T>(_: &'a mut T) -> impl Copy { () }

fn late_bound(x: &i32) -> impl Copy {
    x
    //~^ cannot infer an appropriate lifetime
}

fn early_bound<'a>(x: &'a i32) -> impl Copy {
    x
    //~^ cannot infer an appropriate lifetime
}

fn ambiguous<'a, 'b>(x: &'a [u32], y: &'b [u32]) -> impl Iterator<Item=u32> {
    if x.len() < y.len() {
        x.iter().cloned()
        //~^ cannot infer an appropriate lifetime
    } else {
        y.iter().cloned()
    }
}

fn main() {}
