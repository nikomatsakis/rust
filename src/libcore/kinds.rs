// Copyright 2012 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Primitive traits representing basic 'kinds' of types
//!
//! Rust types can be classified in various useful ways according to
//! intrinsic properties of the type. These classifications, often called
//! 'kinds', are represented as traits.
//!
//! They cannot be implemented by user code, but are instead implemented
//! by the compiler automatically for the types to which they apply.

use self::marker::MarkerTrait;

/// Types able to be transferred across task boundaries.
#[lang="send"]
pub trait Send for Sized? : 'static + MarkerTrait {
    // empty.
}

/// Types with a constant size known at compile-time.
#[lang="sized"]
pub trait Sized for Sized? : MarkerTrait {
    // Empty.
}

/// Types that can be copied by simply copying bits (i.e. `memcpy`).
#[lang="copy"]
pub trait Copy for Sized? : MarkerTrait {
    // Empty.
}

/// Types that can be safely shared between tasks when aliased.
///
/// The precise definition is: a type `T` is `Sync` if `&T` is
/// thread-safe. In other words, there is no possibility of data races
/// when passing `&T` references between tasks.
///
/// As one would expect, primitive types like `u8` and `f64` are all
/// `Sync`, and so are simple aggregate types containing them (like
/// tuples, structs and enums). More instances of basic `Sync` types
/// include "immutable" types like `&T` and those with simple
/// inherited mutability, such as `Box<T>`, `Vec<T>` and most other
/// collection types. (Generic parameters need to be `Sync` for their
/// container to be `Sync`.)
///
/// A somewhat surprising consequence of the definition is `&mut T` is
/// `Sync` (if `T` is `Sync`) even though it seems that it might
/// provide unsynchronised mutation. The trick is a mutable reference
/// stored in an aliasable reference (that is, `& &mut T`) becomes
/// read-only, as if it were a `& &T`, hence there is no risk of a data
/// race.
///
/// Types that are not `Sync` are those that have "interior
/// mutability" in a non-thread-safe way, such as `Cell` and `RefCell`
/// in `std::cell`. These types allow for mutation of their contents
/// even when in an immutable, aliasable slot, e.g. the contents of
/// `&Cell<T>` can be `.set`, and do not ensure data races are
/// impossible, hence they cannot be `Sync`. A higher level example
/// of a non-`Sync` type is the reference counted pointer
/// `std::rc::Rc`, because any reference `&Rc<T>` can clone a new
/// reference, which modifies the reference counts in a non-atomic
/// way.
///
/// For cases when one does need thread-safe interior mutability,
/// types like the atomics in `std::sync` and `Mutex` & `RWLock` in
/// the `sync` crate do ensure that any mutation cannot cause data
/// races.  Hence these types are `Sync`.
///
/// Users writing their own types with interior mutability (or anything
/// else that is not thread-safe) should use the `NoSync` marker type
/// (from `std::kinds::marker`) to ensure that the compiler doesn't
/// consider the user-defined type to be `Sync`.  Any types with
/// interior mutability must also use the `std::cell::UnsafeCell` wrapper
/// around the value(s) which can be mutated when behind a `&`
/// reference; not doing this is undefined behaviour (for example,
/// `transmute`-ing from `&T` to `&mut T` is illegal).
#[lang="sync"]
pub trait Sync for Sized? : MarkerTrait {
    // Empty
}

/// Marker types are special types that are used with unsafe code to
/// inform the compiler of special constraints. Marker types should
/// only be needed when you are creating an abstraction that is
/// implemented using unsafe code. In that case, you may want to embed
/// some of the marker types below into your type.
pub mod marker {
    use super::Copy;
    use clone::Clone;
    use cmp;
    use option::Option;
    use super::Sized;

    macro_rules! impls{
        ($t: ident) => (
            impl<Sized? T> cmp::PartialEq for $t<T> {
                fn eq(&self, _other: &$t<T>) -> bool {
                    true
                }
            }

            impl<Sized? T> cmp::Eq for $t<T> {
            }

            impl<Sized? T> cmp::PartialOrd for $t<T> {
                fn partial_cmp(&self, _other: &$t<T>) -> Option<cmp::Ordering> {
                    Option::Some(cmp::Equal)
                }
            }

            impl<Sized? T> cmp::Ord for $t<T> {
                fn cmp(&self, _other: &$t<T>) -> cmp::Ordering {
                    cmp::Equal
                }
            }

            impl<Sized? T> Copy for $t<T> { }

            impl<Sized? T> Clone for $t<T> {
                fn clone(&self) -> $t<T> {
                    $t
                }
            }
        )
    }

    /// TODO Document me
    pub trait MarkerTrait for Sized? : PhantomSetter<Self> { }
    impl<Sized? T> MarkerTrait for T { }

    /// TODO Document me
    #[lang="phantom_getter"]
    pub trait PhantomGetter<Sized? T> for Sized? { }
    impl<Sized? T, Sized? U> PhantomGetter<T> for U { }

    /// TODO Document me
    #[lang="phantom_setter"]
    pub trait PhantomSetter<Sized? T> for Sized? { }
    impl<Sized? T, Sized? U> PhantomSetter<T> for U { }

    /// TODO Document me
    #[lang="phantom_data"]
    pub struct PhantomData<Sized? T>;

    impls! { PhantomData }

    /// TODO Document me
    #[lang="phantom_cell"]
    pub struct PhantomCell<Sized? T>;

    impls! { PhantomCell }

    /// A marker type whose type parameter `T` is considered to be
    /// covariant with respect to the type itself. This is (typically)
    /// used to indicate that an instance of the type `T` is being stored
    /// into memory and read from, even though that may not be apparent.
    ///
    /// For more information about variance, refer to this Wikipedia
    /// article <http://en.wikipedia.org/wiki/Variance_%28computer_science%29>.
    ///
    /// *Note:* It is very unusual to have to add a covariant constraint.
    /// If you are not sure, you probably want to use `InvariantType`.
    ///
    /// # Example
    ///
    /// Given a struct `S` that includes a type parameter `T`
    /// but does not actually *reference* that type parameter:
    ///
    /// ```ignore
    /// use std::mem;
    ///
    /// struct S<T> { x: *() }
    /// fn get<T>(s: &S<T>) -> T {
    ///    unsafe {
    ///        let x: *T = mem::transmute(s.x);
    ///        *x
    ///    }
    /// }
    /// ```
    ///
    /// The type system would currently infer that the value of
    /// the type parameter `T` is irrelevant, and hence a `S<int>` is
    /// a subtype of `S<Box<int>>` (or, for that matter, `S<U>` for
    /// any `U`). But this is incorrect because `get()` converts the
    /// `*()` into a `*T` and reads from it. Therefore, we should include the
    /// a marker field `CovariantType<T>` to inform the type checker that
    /// `S<T>` is a subtype of `S<U>` if `T` is a subtype of `U`
    /// (for example, `S<&'static int>` is a subtype of `S<&'a int>`
    /// for some lifetime `'a`, but not the other way around).
    #[lang="covariant_type"]
    // SNAP c9f6d69 -- cannot deprecate until snapshot
    // #[deprecated = "Replace `CovariantType<T>` with `PhantomData<T>`"]
    pub struct CovariantType<Sized? T>;

    impls! { CovariantType }

    /// A marker type whose type parameter `T` is considered to be
    /// contravariant with respect to the type itself. This is (typically)
    /// used to indicate that an instance of the type `T` will be consumed
    /// (but not read from), even though that may not be apparent.
    ///
    /// For more information about variance, refer to this Wikipedia
    /// article <http://en.wikipedia.org/wiki/Variance_%28computer_science%29>.
    ///
    /// *Note:* It is very unusual to have to add a contravariant constraint.
    /// If you are not sure, you probably want to use `InvariantType`.
    ///
    /// # Example
    ///
    /// Given a struct `S` that includes a type parameter `T`
    /// but does not actually *reference* that type parameter:
    ///
    /// ```
    /// use std::mem;
    ///
    /// struct S<T> { x: *const () }
    /// fn get<T>(s: &S<T>, v: T) {
    ///    unsafe {
    ///        let x: fn(T) = mem::transmute(s.x);
    ///        x(v)
    ///    }
    /// }
    /// ```
    ///
    /// The type system would currently infer that the value of
    /// the type parameter `T` is irrelevant, and hence a `S<int>` is
    /// a subtype of `S<Box<int>>` (or, for that matter, `S<U>` for
    /// any `U`). But this is incorrect because `get()` converts the
    /// `*()` into a `fn(T)` and then passes a value of type `T` to it.
    ///
    /// Supplying a `ContravariantType` marker would correct the
    /// problem, because it would mark `S` so that `S<T>` is only a
    /// subtype of `S<U>` if `U` is a subtype of `T`; given that the
    /// function requires arguments of type `T`, it must also accept
    /// arguments of type `U`, hence such a conversion is safe.
    #[lang="contravariant_type"]
    // SNAP c9f6d69 -- cannot deprecate until snapshot
    // #[deprecated = "Replace `ContravariantType<T>` with `PhantomData<fn() -> T>`"]
    pub struct ContravariantType<Sized? T>;

    impls! { ContravariantType }

    /// A marker type whose type parameter `T` is considered to be
    /// invariant with respect to the type itself. This is (typically)
    /// used to indicate that instances of the type `T` may be read or
    /// written, even though that may not be apparent.
    ///
    /// For more information about variance, refer to this Wikipedia
    /// article <http://en.wikipedia.org/wiki/Variance_%28computer_science%29>.
    ///
    /// # Example
    ///
    /// The Cell type is an example which uses unsafe code to achieve
    /// "interior" mutability:
    ///
    /// ```
    /// pub struct Cell<T> { value: T }
    /// # fn main() {}
    /// ```
    ///
    /// The type system would infer that `value` is only read here and
    /// never written, but in fact `Cell` uses unsafe code to achieve
    /// interior mutability.
    #[lang="invariant_type"]
    // SNAP c9f6d69 -- cannot deprecate until snapshot
    // #[deprecated = "Replace `InvariantType<T>` with `PhantomCell<T>`"]
    pub struct InvariantType<Sized? T>;

    impls! { InvariantType }

    /// As `CovariantType`, but for lifetime parameters. Using
    /// `CovariantLifetime<'a>` indicates that it is ok to substitute
    /// a *longer* lifetime for `'a` than the one you originally
    /// started with (e.g., you could convert any lifetime `'foo` to
    /// `'static`). You almost certainly want `ContravariantLifetime`
    /// instead, or possibly `InvariantLifetime`. The only case where
    /// it would be appropriate is that you have a (type-casted, and
    /// hence hidden from the type system) function pointer with a
    /// signature like `fn(&'a T)` (and no other uses of `'a`). In
    /// this case, it is ok to substitute a larger lifetime for `'a`
    /// (e.g., `fn(&'static T)`), because the function is only
    /// becoming more selective in terms of what it accepts as
    /// argument.
    ///
    /// For more information about variance, refer to this Wikipedia
    /// article <http://en.wikipedia.org/wiki/Variance_%28computer_science%29>.
    #[lang="covariant_lifetime"]
    #[deriving(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    // SNAP c9f6d69 -- cannot deprecate until snapshot
    // #[deprecated = "Replace `CovariantLifetime<'a>` with `PhantomData<&'a ()>`"]
    pub struct CovariantLifetime<'a>;

    /// As `ContravariantType`, but for lifetime parameters. Using
    /// `ContravariantLifetime<'a>` indicates that it is ok to
    /// substitute a *shorter* lifetime for `'a` than the one you
    /// originally started with (e.g., you could convert `'static` to
    /// any lifetime `'foo`). This is appropriate for cases where you
    /// have an unsafe pointer that is actually a pointer into some
    /// memory with lifetime `'a`, and thus you want to limit the
    /// lifetime of your data structure to `'a`. An example of where
    /// this is used is the iterator for vectors.
    ///
    /// For more information about variance, refer to this Wikipedia
    /// article <http://en.wikipedia.org/wiki/Variance_%28computer_science%29>.
    #[lang="contravariant_lifetime"]
    #[deriving(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    // SNAP c9f6d69 -- cannot deprecate until snapshot
    // #[deprecated = "Replace `ContravariantLifetime<'a>` with `PhantomData<fn() -> &'a ()>`"]
    pub struct ContravariantLifetime<'a>;

    /// As `InvariantType`, but for lifetime parameters. Using
    /// `InvariantLifetime<'a>` indicates that it is not ok to
    /// substitute any other lifetime for `'a` besides its original
    /// value. This is appropriate for cases where you have an unsafe
    /// pointer that is actually a pointer into memory with lifetime `'a`,
    /// and this pointer is itself stored in an inherently mutable
    /// location (such as a `Cell`).
    #[lang="invariant_lifetime"]
    #[deriving(PartialEq,Eq,PartialOrd,Ord,Clone)]
    // SNAP c9f6d69 -- cannot deprecate until snapshot
    // #[deprecated = "Replace `InvariantLifetime<'a>` with `PhantomCell<&'a ()>`"]
    pub struct InvariantLifetime<'a>;

    /// A type which is considered "not sendable", meaning that it cannot
    /// be safely sent between tasks, even if it is owned. This is
    /// typically embedded in other types, such as `Gc`, to ensure that
    /// their instances remain thread-local.
    #[lang="no_send_bound"]
    #[deriving(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct NoSend;

    /// A type which is considered "not POD", meaning that it is not
    /// implicitly copyable. This is typically embedded in other types to
    /// ensure that they are never copied, even if they lack a destructor.
    #[lang="no_copy_bound"]
    #[deriving(Clone, PartialEq, Eq, PartialOrd, Ord)]
    #[allow(missing_copy_implementations)]
    pub struct NoCopy;

    /// A type which is considered "not sync", meaning that
    /// its contents are not threadsafe, hence they cannot be
    /// shared between tasks.
    #[lang="no_sync_bound"]
    #[deriving(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct NoSync;

    /// A type which is considered managed by the GC. This is typically
    /// embedded in other types.
    #[lang="managed_bound"]
    #[deriving(Clone, PartialEq, Eq, PartialOrd, Ord)]
    #[allow(missing_copy_implementations)]
    pub struct Managed;
}

