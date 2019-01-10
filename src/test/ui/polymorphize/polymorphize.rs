// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize -Zpolymorphize-dump -Zpolymorphize-duplicates
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

    // Invoke each function so that they are considered by the collector.
    no_use::<u32>();
    no_use::<u16>();

    no_dependency_because_pointer::<u32>(&2);
    no_dependency_because_pointer::<u16>(&2);

    dependency_because_unsized_pointer::<u32>(&2);
    dependency_because_unsized_pointer::<u16>(&2);

    depend_size_alignment::<u32>(&2);
    depend_size_alignment::<u16>(&2);

    depend_size_alignment_indirect::<u32>(&2);
    depend_size_alignment_indirect::<u16>(&2);

    no_dependency_indirect::<u32>(&2);
    no_dependency_indirect::<u16>(&2);
}
