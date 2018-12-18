// Tests focused on trait dispatch.
//
// compile-flags: -Zpolymorphize

#![allow(warnings)]

fn depend_trait_dispatch<T: Clone>(t: &T) -> T {
    //~^ ERROR some polymorphic dependencies found
    t.clone()
}

fn depend_trait_dispatch_indirect<T: Clone>(t: &T) -> T {
    //~^ ERROR some polymorphic dependencies found
    depend_trait_dispatch(t)
}

fn depend_trait_dispatch_ref_indirect<T: Clone>(t: &T) -> &T {
    //~^ ERROR no polymorphic dependencies found
    //
    // FIXME this should be a dependency, but right now we see that we
    // are invoking `depend_trait_dispatch` with a type parameter of
    // `&T`, and that has a fixed size (which isn't really relevant)
    // so we skip it.

    depend_trait_dispatch::<&T>(&t)
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
