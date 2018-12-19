// Simple test for the polymorphize analysis code.
//
// compile-flags: -Zpolymorphize

#![allow(warnings)]

struct EmbedRef<'a, T: ?Sized> {
    t: &'a T
}

fn no_dependency_because_pointer<T>(t: &T) -> &T {
    //~^ ERROR no polymorphic dependencies found
    t
}

fn dependency_because_unsized_pointer<T: ?Sized>(t: &T) -> &T {
    //~^ ERROR some polymorphic dependencies found
    t
}

fn dependency_because_embed_ref_unsized<T: ?Sized>(t: &T) -> EmbedRef<'_, T> {
    //~^ ERROR some polymorphic dependencies found
    EmbedRef { t }
}

fn dependency_because_embed_ref_sized<T>(t: &T) -> EmbedRef<'_, T> {
    //~^ ERROR no polymorphic dependencies found
    //
    // Here, the size of `EmbedRef` is known up front.
    EmbedRef { t }
}

fn no_dependency_because_unsized_pointer_indirect<T>(t: &T) {
    //~^ ERROR no polymorphic dependencies found

    // Although `dependency_because_unsized_pointer` has a dependency
    // (as T is not known to be sized), *this* function knows that `T`
    // is sized, and that's good enough.
    dependency_because_unsized_pointer::<T>(t);
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
