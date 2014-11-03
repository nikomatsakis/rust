// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.
//
// ignore-lexer-test FIXME #15879

#![allow(bivariance)]

use std::kinds::marker;

// Test syntax checks for `Sized?` syntax.

trait T1 for Sized? : marker::Covariant {}
pub trait T2 for Sized? : marker::Covariant {}
trait T3<X: T1> for Sized? : T2 {}
trait T4<Sized? X : marker::Covariant> {}
trait T5<Sized? X : marker::Covariant, Y> {}
trait T6<Y, Sized? X : marker::Covariant> {}
trait T7<Sized? X : marker::Covariant, Sized? Y : marker::Covariant> {}
trait T8<Sized? X : T2> {}
struct S1<Sized? X> { marker: marker::CovariantType<X> }
enum E<Sized? X> { Dummy(marker::CovariantType<X>) }
impl <Sized? X> T1 for S1<X> {}
fn f<Sized? X>() {}
type TT<T> = T;

pub fn main() {
}
