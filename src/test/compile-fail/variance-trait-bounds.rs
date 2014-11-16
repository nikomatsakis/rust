// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![deny(bivariance)]
#![allow(dead_code)]

// Check that bounds on type parameters (at least in types)
// do not which is only used in a trait bound is
// not considered bivariant.

#[rustc_variance]
trait Getter<T> { //~ ERROR types=[[+];[o];[];[]]
    fn get(&self) -> T;
}

#[rustc_variance]
trait Setter<T> { //~ ERROR types=[[-];[o];[];[]]
    fn get(&self, T);
}

#[rustc_variance]
struct TestStruct<U,T:Getter<U>> { //~ ERROR types=[[+, +];[];[];[]]
    t: T, u: U
}

#[rustc_variance]
enum TestEnum<U,T:Getter<U>> {//~ ERROR types=[[+, +];[o];[]]
    Foo(T)
}

#[rustc_variance]
trait TestTrait<U,T:Getter<U>> { //~ ERROR types=[[+, +];[o];[]]
    fn getter(&self) -> T;
}

#[rustc_variance]
trait TestTrait2<U> : Getter<U> { //~ ERROR types=[[+];[o];[]]
}

#[rustc_variance]
trait TestTrait3<U> { //~ ERROR types=[[+];[o];[]]
    fn getter<T:Getter<U>>(&self);
}

#[rustc_variance]
struct TestContraStruct<U,T:Setter<U>> { //~ ERROR types=[[-, +];[o];[]]
    t: T
}

#[rustc_variance]
struct TestBox<U,T:Getter<U>+Setter<U>> { //~ ERROR types=[[o, +];[o];[]]
    t: T
}

pub fn main() { }
