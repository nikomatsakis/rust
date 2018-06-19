// Copyright 2016 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test where gathering of implied bounds was triggering a normalization
// that caused region obligations to be injected into NLL type-checking
// at a time they were not expected.

// compile-flags:-Zborrowck=mir -Zverbose
// run-pass

struct Map<A, F> where A: Future {
    a: A,
    f: F,
}

trait Future {
    type Item;
    type Error;

    fn tailcall(&mut self) -> Option<Box<Future<Item=Self::Item, Error=Self::Error>>>;
}

impl<A, F, U> Future for Map<A, F>
where
    A: Future,
    F: FnOnce(A::Item) -> U + Send + 'static,
    U: Send + 'static,
{
    type Item = U;
    type Error = A::Error;

    fn tailcall(&mut self)
                -> Option<Box<Future<Item=Self::Item, Error=Self::Error>>> {
        None
    }
}

fn main() {}
