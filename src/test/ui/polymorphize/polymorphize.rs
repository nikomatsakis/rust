// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize -Zpolymorphize-dump
// compile-pass

#![allow(warnings)]

fn no_use<T>() {
    //~^ ERROR no polymorphic dependencies found
}

fn no_dependency_because_pointer<T>(t: &T) -> &T {
    //~^ ERROR no polymorphic dependencies found
    t
}

fn dependency_because_unsized_pointer<T: ?Sized>(t: &T) -> &T {
    //~^ ERROR some polymorphic dependencies found
    t
}

fn depend_size_alignment<T: Copy>(t: &T) -> T {
    //~^ ERROR some polymorphic dependencies found
    *t
}

fn depend_size_alignment_indirect<T: Copy>(t: &T) -> T {
    //~^ ERROR some polymorphic dependencies found
    depend_size_alignment(t)
}

fn no_dependency_indirect<T: Copy>(t: &T) -> u32 {
    //~^ ERROR no polymorphic dependencies found
    depend_size_alignment(&22)
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
