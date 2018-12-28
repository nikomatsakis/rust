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
    //~^ ERROR some polymorphic dependencies found
}

fn dependency_because_drop_box_T<T>(data: Box<T>) {
    //~^ ERROR some polymorphic dependencies found
}

fn no_dependency_because_drop_ref_T<T>(data: &T) {
    //~^ ERROR no polymorphic dependencies found
}

fn no_dependency_because_indirect_drop_ref_T<T>(data: &T) {
    //~^ ERROR no polymorphic dependencies found

    dependency_because_drop_T::<&T>(data);
}

fn no_dependency_because_indirect_drop_ref_u32() {
    //~^ ERROR no polymorphic dependencies found

    dependency_because_drop_T::<&u32>(&22);
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
