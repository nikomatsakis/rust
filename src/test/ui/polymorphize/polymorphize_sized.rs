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

fn dependency_because_unsized_pointer_indirect<T>(t: &T) {
    //~^ ERROR some polymorphic dependencies found
    //
    // FIXME -- Here, we know that `T: Sized`, and really that is all
    // that is needed to resolve the sizes for types in
    // `dependency_because_unsized_pointer`, but because we are
    // imprecise, we don't figure that out.
    dependency_because_unsized_pointer::<T>(t);
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
