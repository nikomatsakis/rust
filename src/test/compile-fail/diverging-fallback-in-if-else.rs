// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Test that we do not allow "type variable divergence" to propagate
// from one arm of a match when others do not diverge.

fn main() {
    // The type of _ is unconstrained it used to default to `()` but
    // that was basically a bug. The flaw was that the type of
    // `return` was divering, and hence we considered the type
    // variable for the type of `match` to diverge, but that is
    // obviously wrong, since there is no dataflow from the `Err(_)`
    // arm into the variable `_x`.
    let _x = if true {
        Some(Default::default())
            //~^ ERROR type annotations needed
    } else {
        return
    };
}

