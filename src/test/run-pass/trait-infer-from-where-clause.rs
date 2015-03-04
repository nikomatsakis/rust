// Copyright 2013 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Tests a case where we need to consider the where-clauses of `Foo`,
// and not just its supetraits, to infer that `A:Foo` holds.
// Issue #20671.

trait Foo<T> {
    fn foo(&self) -> &T;
}

trait Bar<A> where A: Foo<Self> {
    fn dummy(&self, a: A);
}

fn foobar<A, B: Bar<A>>(a: &A) -> &B {
   a.foo()
}

fn main() { }
