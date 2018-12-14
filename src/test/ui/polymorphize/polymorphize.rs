// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize

#![allow(warnings)]

fn no_use<T>() {
    //~^ ERROR no polymorphic dependencies found
}

fn no_dependency_because_pointer<T>(t: &T) -> &T {
    //~^ ERROR no polymorphic dependencies found
    t
}

fn depend_size_alignment<T: Copy>(t: &T) -> T {
    //~^ ERROR no polymorphic dependencies found
    // FIXME -- this should depend on the size/alignment of `T`
    *t
}

fn depend_size_alignment_indirect<T: Copy>(t: &T) -> T {
    //~^ ERROR no polymorphic dependencies found
    // FIXME -- this should depend on the size/alignment of `T`
    depend_size_alignment(t)
}

fn no_dependency_indirect<T: Copy>(t: &T) -> u32 {
    //~^ ERROR no polymorphic dependencies found
    depend_size_alignment(&22)
}

fn depend_trait_dispatch<T: Clone>(t: &T) -> T {
    //~^ ERROR some polymorphic dependencies found
    t.clone()
}

fn depend_trait_dispatch_indirect<T: Clone>(t: &T) -> T {
    //~^ ERROR no polymorphic dependencies found
    // FIXME -- this should depend on trait methods around `T`
    depend_trait_dispatch(t)
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
