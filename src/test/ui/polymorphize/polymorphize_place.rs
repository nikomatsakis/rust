// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize -Zpolymorphize-dump
// compile-pass

#![allow(warnings)]

struct OffsetDependent<T> {
    t: T,
    count: u32,
}

fn dependency_because_offset_depends_on_T<T>(parameter: &OffsetDependent<T>) -> u32 {
    //~^ ERROR some polymorphic dependencies found
    parameter.count
}

fn dependency_because_offset_depends_on_T_sized<T: ?Sized>(parameter: &OffsetDependent<&T>) -> u32 {
    //~^ ERROR some polymorphic dependencies found
    parameter.count
}

fn no_dependency_because_offset<T>(parameter: &OffsetDependent<&T>) -> u32 {
    //~^ ERROR no polymorphic dependencies found
    //
    // Correct: size/alignment of `T` known.
    parameter.count
}

fn dependency_because_index_depends_on_T<T>(parameters: &[T]) -> &T {
    //~^ ERROR some polymorphic dependencies found
    &parameters[0]
}

fn no_dependency_because_index_depends_on_sized_pointer<'a, T>(parameters: &'a [&'a T]) -> &'a T {
    //~^ ERROR no polymorphic dependencies found
    &parameters[0]
}

fn main() {
    //~^ ERROR no polymorphic dependencies found

    // Invoke each function so that they are considered by the collector.
    no_dependency_because_offset::<u32>(&OffsetDependent { t: &22, count: 2 });
    no_dependency_because_offset::<u16>(&OffsetDependent { t: &22, count: 2 });

    dependency_because_offset_depends_on_T_sized::<u32>(&OffsetDependent { t: &22, count: 2 });
    dependency_because_offset_depends_on_T_sized::<u16>(&OffsetDependent { t: &22, count: 2 });
    dependency_because_offset_depends_on_T_sized::<str>(&OffsetDependent { t: "foo", count: 2 });

    dependency_because_offset_depends_on_T::<u32>(&OffsetDependent { t: 22, count: 2 });
    dependency_because_offset_depends_on_T::<u16>(&OffsetDependent { t: 22, count: 2 });

    dependency_because_index_depends_on_T::<u32>(&[2, 3, 4]);
    dependency_because_index_depends_on_T::<u16>(&[2, 3, 4]);

    no_dependency_because_index_depends_on_sized_pointer::<u32>(&[&2, &3, &4]);
    no_dependency_because_index_depends_on_sized_pointer::<u16>(&[&2, &3, &4]);
}
