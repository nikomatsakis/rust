// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize -Zpolymorphize-dump
// compile-pass

#![allow(warnings)]

struct OffsetDependent<T> {
    t: T,
    count: u32,
}

fn dependency_because_drop_T<T>(data: T) {
    //~^ ERROR no polymorphic dependencies found
    //
    // We have to drop `data`, and to know what to run, we have to know what `T` is.
    //
    // FIXME-- we don't presently see the dependency
}

fn dependency_because_drop_box_T<T>(data: Box<T>) {
    //~^ ERROR no polymorphic dependencies found
    //
    // We have to drop `data`, and to know what to run, we have to
    // know what `T` is.  This is true even though the *size* of
    // `data` is known.
    //
    // FIXME-- we don't presently see the dependency
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
