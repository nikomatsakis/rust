// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// This test was derived from the wasm and parsell crates.  They
// stopped compiling when #32330 is fixed.

#![feature(unboxed_closures)]

use std::str::Chars;

pub trait HasOutput<Ch, Str> {
    type Output;
}

#[derive(Clone, PartialEq, Eq, Hash, Ord, PartialOrd, Debug)]
pub enum Token<'a> {
    Begin(&'a str)
}

fn mk_unexpected_char_err(u: &u32) -> Option<&'static i32> {
    unimplemented!()
}

fn foo<'a>(data: &mut Chars<'a>) {
    bar(mk_unexpected_char_err) //~ ERROR type mismatch
}

fn bar<F>(t: F)
    // No type can satisfy this requirement, since `'a` does not
    // appear in any of the input types:
    where F: for<'a> Fn(&'a u32) -> Option<&'a i32>
{
}

fn main() {
}
