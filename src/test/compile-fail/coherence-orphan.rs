// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// aux-build:coherence-orphan-lib.rs

extern crate lib = "coherence-orphan-lib";

use lib::{TheirTrait,TheirStruct,TheirSmartPointer};

trait MyTrait { fn my_method() { } }
struct MyStruct { foo: int }
struct MySmartPointer<T> { foo: *T }

// Disallowed. These would be an orphan implementations.

impl TheirTrait for TheirStruct { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for (TheirStruct, int) { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for (uint, TheirStruct, int) { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for TheirSmartPointer<TheirStruct> { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for u8 { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for ~str { } //~ ERROR both trait and type are not defined in this crate
impl<'a> TheirTrait for |MyStruct|:'a { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for fn(MyStruct) { } //~ ERROR both trait and type are not defined in this crate
impl TheirTrait for *int { } //~ ERROR both trait and type are not defined in this crate

// Allowed because local types.

impl TheirTrait for MyStruct { }
impl TheirTrait for MySmartPointer<TheirStruct> { }
impl TheirTrait for TheirSmartPointer<MyStruct> { }
impl TheirTrait for (MyStruct, TheirStruct) { }
impl TheirTrait for (uint, MyStruct, int) { }
impl TheirTrait for ~[MyStruct] { }
impl TheirTrait for ~MyStruct { }
impl<'a> TheirTrait for &'a MyStruct { }
impl<'a> TheirTrait for &'a mut MyStruct { }
impl<'a> TheirTrait for ~MyTrait { }
impl TheirTrait for *MyStruct { }

// Allowed because local traits.

impl MyTrait for TheirStruct { }
impl MyTrait for TheirSmartPointer<TheirStruct> { }

pub fn main() { }
