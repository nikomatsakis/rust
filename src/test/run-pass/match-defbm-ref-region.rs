// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// FIXME(tschottdorf): Uncommenting `// r` below, get:
//
// error[E0597]: `(x:std::prelude::v1::Some).0` does not live long enough
//   --> /Users/tschottdorf/rust/binding-modes/src/test/run-pass/match-defbm-ref-region.rs:14:14
//    |
// 14 |         Some(r) => r,
//    |              ^ does not live long enough
// ...
// 17 | }
//    | - borrowed value only lives until here
//    |
// note: borrowed value must be valid for the lifetime 'a as defined on the function body at 11:1...
//   --> /Users/tschottdorf/rust/binding-modes/src/test/run-pass/match-defbm-ref-region.rs:11:1
//    |
// 11 | / fn foo<'a, 'b>(x: &'a &'b Option<u32>) -> &'a u32 {
// 12 | |     let x: &'a &'a Option<u32> = x;
// 13 | |     match x {
// 14 | |         Some(r) => r,
// 15 | |         &None => panic!(),
// 16 | |     }
// 17 | | }
//    | |_^

fn foo<'a, 'b>(x: &'a &'b Option<u32>) -> &'a u32 {
    let x: &'a &'a Option<u32> = x;
    match x {
        Some(r) => {
            let _: &u32 = r;
            &5
            // r
        },
        &None => panic!(),
    }
}

pub fn main() {
    let x = Some(5);
    foo(&&x);
}
