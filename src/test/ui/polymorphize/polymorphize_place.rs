// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize

#![allow(warnings)]

struct OffsetDependent<T> {
    t: T,
    count: u32,
}

fn dependency_because_offset_depends_on_T<T>(parameter: &OffsetDependent<T>) -> u32 {
    //~^ ERROR no polymorphic dependencies found
    //
    // FIXME -- the offset of the `count` field depends on size/alignment of `T`
    parameter.count
}

fn dependency_because_offset_depends_on_T_sized<T: ?Sized>(parameter: &OffsetDependent<&T>) -> u32 {
    //~^ ERROR no polymorphic dependencies found
    //
    // FIXME -- the offset of the `count` field depends on whether `T` is sized
    parameter.count
}

fn no_dependency_because_offset<T>(parameter: &OffsetDependent<&T>) -> u32 {
    //~^ ERROR no polymorphic dependencies found
    //
    // Correct: size/alignment of `T` known.
    parameter.count
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
