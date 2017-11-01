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
#![allow(warnings)]

use std::fmt::Debug;

fn any_lifetime<'a>() -> &'a u32 { &5 }

fn static_lifetime() -> &'static u32 { &5 }

fn any_lifetime_as_static_impl_trait() -> impl Debug {
    any_lifetime()
}

fn lifetimes_as_static_impl_trait() -> impl Debug {
        static_lifetime()
}

trait Foo<'a> {}
impl<'a> Foo<'a> for u32 {}

fn foo<'b>() -> impl for<'a> Foo<'a> { 5 }

fn closure_hrtb() -> impl for<'a> Fn(&'a u32) { |_| () }

fn mixed_lifetimes<'a>() -> impl for<'b: 'a> Fn(&'b u32) { |_| () }

fn mixed_as_static() -> impl Fn(&'static u32) { mixed_lifetimes() }

trait MultiRegion<'a, 'b> {}
struct MultiRegionStruct<'a, 'b>(&'a u32, &'b u32);
impl<'a, 'b> MultiRegion<'a, 'b> for MultiRegionStruct<'a, 'b> {}

fn finds_least_region<'a: 'b, 'b>(x: &'a u32, y: &'b u32) -> impl MultiRegion<'a, 'b>
{
    MultiRegionStruct(x, y)
}

fn explicit_bound<'a: 'b, 'b>(x: &'a u32, y: &'b u32) -> impl MultiRegion<'a, 'b> + 'b
{
    MultiRegionStruct(x, y)
}

fn main() {}
