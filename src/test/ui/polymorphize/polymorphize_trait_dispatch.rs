// Tests focused on trait dispatch.
//
// compile-flags: -Zpolymorphize=0 -Zpolymorphize-dump -Zpolymorphize-duplicates
// compile-pass

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

    // Invoke each function so that they are considered by the collector.
    depend_trait_dispatch::<u32>(&3);
    depend_trait_dispatch::<u16>(&3);

    depend_trait_dispatch_indirect::<u32>(&3);
    depend_trait_dispatch_indirect::<u16>(&3);

    depend_trait_dispatch_ref_indirect::<u32>(&3);
    depend_trait_dispatch_ref_indirect::<u16>(&3);
}
