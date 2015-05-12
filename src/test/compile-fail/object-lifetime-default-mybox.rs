// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test that the `SomeTrait` in `&'a MyBox<SomeTrait>` expands the
// same way as `MyBox<SomeTrait>`

#![allow(dead_code)]
#![allow(unused_variables)]
#![feature(rustc_attrs)]

trait SomeTrait {
    fn dummy(&self) { }
}

struct MyBox<T:?Sized> {
    r: Box<T>
}

fn deref<T>(ss: &T) -> T {
    // produces the type of a deref without worrying about whether a
    // move out would actually be legal
    loop { }
}

fn load0(ss: &MyBox<SomeTrait>) -> MyBox<SomeTrait> {
    deref(ss)
}

fn load1<'a,'b>(a: &'a MyBox<SomeTrait>,
                b: &'b MyBox<SomeTrait>)
                -> MyBox<SomeTrait>
{
    deref(a)
}

#[rustc_error]
fn main() { //~ ERROR compilation successful
}
