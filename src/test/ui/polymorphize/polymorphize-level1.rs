// Test of level 1 polymorphization analysis code.
//
// compile-flags: -Zpolymorphize=1 -Zpolymorphize-dump -Zpolymorphize-duplicates
// compile-pass

struct OffsetDependent<T> {
    t: T,
    count: u32,
}

fn offset_of_dependency<T>(parameter: &OffsetDependent<T>) -> u32 {
    //~^ ERROR some polymorphic dependencies found
    parameter.count
}

fn drop_dependency<T>(data: T) {
    //~^ ERROR some polymorphic dependencies found
}

fn size_alignment_dependency<T: ?Sized>(t: &T) -> &T {
    //~^ ERROR no polymorphic dependencies found
    t
}

fn trait_method_dependency<T: Clone>(t: &T) -> T {
    //~^ ERROR some polymorphic dependencies found
    t.clone()
}

fn index_into_dependency<T>(parameters: &[T]) -> &T {
    //~^ ERROR no polymorphic dependencies found
    &parameters[0]
}

fn main() {
    //~^ ERROR no polymorphic dependencies found

    // Invoke each function so that they are considered by the collector.
    index_into_dependency::<u32>(&[2, 3, 4]);
    index_into_dependency::<u16>(&[2, 3, 4]);

    trait_method_dependency::<u32>(&3);
    trait_method_dependency::<u16>(&3);

    size_alignment_dependency::<u32>(&2);
    size_alignment_dependency::<u16>(&2);

    drop_dependency::<u32>(3);
    drop_dependency::<u16>(3);

    offset_of_dependency::<u32>(&OffsetDependent { t: 22, count: 2 });
    offset_of_dependency::<u16>(&OffsetDependent { t: 22, count: 2 });
}
