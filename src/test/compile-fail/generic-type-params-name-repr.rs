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

struct A;
struct B;
struct C;
struct Foo<T = A, U = B, V = C>(marker::CovariantType<(T,U,V)>);

struct Hash<T>(marker::CovariantType<T>);
struct HashMap<K, V, H = Hash<K>>(marker::CovariantType<(K,V,H)>);

fn main() {
    // Ensure that the printed type doesn't include the default type params...
    let _: Foo<int> = ();
    //~^ ERROR mismatched types: expected `Foo<int>`, found `()`

    // ...even when they're present, but the same types as the defaults.
    let _: Foo<int, B, C> = ();
    //~^ ERROR mismatched types: expected `Foo<int>`, found `()`

    // Including cases where the default is using previous type params.
    let _: HashMap<String, int> = ();
    //~^ ERROR mismatched types: expected `HashMap<collections::string::String, int>`, found `()`
    let _: HashMap<String, int, Hash<String>> = ();
    //~^ ERROR mismatched types: expected `HashMap<collections::string::String, int>`, found `()`

    // But not when there's a different type in between.
    let _: Foo<A, int, C> = ();
    //~^ ERROR mismatched types: expected `Foo<A, int>`, found `()`

    // And don't print <> at all when there's just defaults.
    let _: Foo<A, B, C> = ();
    //~^ ERROR mismatched types: expected `Foo`, found `()`
}
