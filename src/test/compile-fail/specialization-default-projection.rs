// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Make sure we can't project defaulted associated types

trait Foo {
    type Assoc;
}

impl<T> Foo for T {
    default type Assoc = ();
}

impl Foo for u8 {
    type Assoc = String;
}

fn generic<T>() -> <T as Foo>::Assoc {
    () //~ ERROR
}

fn main() {
    let s: String = generic::<u8>();
    println!("{}", s); // bad news
}
