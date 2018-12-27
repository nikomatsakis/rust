// Tests focused on trait dispatch.
//
// compile-flags: -Zpolymorphize -Zpolymorphize-dump

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
    //~^ ERROR some polymorphic dependencies found
    depend_trait_dispatch::<&T>(&t)
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
