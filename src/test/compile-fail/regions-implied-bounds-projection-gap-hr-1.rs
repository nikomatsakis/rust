// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// The "projection gap" is particularly "fun" around higher-ranked
// projections.  This is because the current code is hard-coded to say
// that a projection that contains escaping regions, like `<T as
// Trait2<'y, 'z>>::Foo` where `'z` is bound, can only be found to
// outlive a region if all components that appear free (`'y`, where)
// outlive that region. However, we DON'T add those components to the
// implied bounds set, but rather we treat projections with escaping
// regions as opaque entities, just like projections without escaping
// regions.

trait Trait1<T> { }

trait Trait2<'a, 'b> {
    type Foo;
}

fn wf<T>() { }

// As a side-effect of the conservative process above, this argument
// is not automatically considered well-formed, since for it to be WF,
// we would need to know that `'y: 'x`, but we do not infer that.
fn callee<'x, 'y, T>(
    t: &'x for<'z> Trait1< <T as Trait2<'y, 'z>>::Foo >)
    //~^ ERROR reference has a longer lifetime than the data it references
{
    wf::<&'x &'y i32>();
}

fn main() { }
