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
    //~^ ERROR no polymorphic dependencies found
    //
    // FIXME-- we do depend on `T`, because size of `&T` depends on knowning whether
    // `T` is sized or not
    t
}

fn dependency_because_embed_ref_unsized<T: ?Sized>(t: &T) -> EmbedRef<'_, T> {
    //~^ ERROR no polymorphic dependencies found
    //
    // FIXME-- we do depend on `T`, because size of `&T` depends on knowning whether
    // `T` is sized or not
    EmbedRef { t }
}

fn dependency_because_embed_ref_sized<T>(t: &T) -> EmbedRef<'_, T> {
    //~^ ERROR no polymorphic dependencies found
    //
    // Here, the size of `EmbedRef` is known up front.
    EmbedRef { t }
}

fn main() {
    //~^ ERROR no polymorphic dependencies found
}
