// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test that we report an error for unused type parameters in types.

struct SomeStruct<A> { x: uint } //~ ERROR E0161
enum SomeEnum<A> { Nothing } //~ ERROR E0161
trait SomeTrait<A> { fn foo(&self); } //~ ERROR E0161

fn main() {}
