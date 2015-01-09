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

struct A;
struct B;
struct C;
struct Foo<T = A, U = B, V = C>(marker::CovariantType<(T,U,V)>);

struct Hash<T>(marker::CovariantType<T>);
struct HashMap<K, V, H = Hash<K>>(marker::CovariantType<(K,V,H)>);

fn main() {
    // Ensure that the printed type doesn't include the default type params...
    let _: Foo<isize> = ();
    //~^ ERROR mismatched types: expected `Foo<isize>`, found `()`

    // ...even when they're present, but the same types as the defaults.
    let _: Foo<isize, B, C> = ();
    //~^ ERROR mismatched types: expected `Foo<isize>`, found `()`

    // Including cases where the default is using previous type params.
    let _: HashMap<String, isize> = ();
    //~^ ERROR mismatched types: expected `HashMap<collections::string::String, isize>`, found `()`
    let _: HashMap<String, isize, Hash<String>> = ();
    //~^ ERROR mismatched types: expected `HashMap<collections::string::String, isize>`, found `()`

    // But not when there's a different type in between.
    let _: Foo<A, isize, C> = ();
    //~^ ERROR mismatched types: expected `Foo<A, isize>`, found `()`

    // And don't print <> at all when there's just defaults.
    let _: Foo<A, B, C> = ();
    //~^ ERROR mismatched types: expected `Foo`, found `()`
}
