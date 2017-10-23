// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(conservative_impl_trait)]

use std::fmt::Debug;

fn foo<'a>(x: &'a i32) -> impl Debug + 'a {
    x
}

fn foo_not_static() -> impl Debug + 'static {
    let mut x = 5;
    x += 5;
    foo(&x)
    //~^ ERROR `x` does not live long enough
}

trait Any {}
impl<T> Any for T {}

// Check that type parameters are captured and not considered 'static
fn whatever<T>(x: T) -> impl Any + 'static {
    x
    //~^ ERROR the parameter type `T` may not live long enough
}

fn move_lifetime_into_fn<'a, 'b>(x: &'a u32, y: &'b u32) -> impl Fn(&'a u32) {
    move |_| println!("{}", y)
}

fn main() {}
