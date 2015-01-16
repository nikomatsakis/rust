// Copyright 2012-2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Primitive traits and marker types representing basic 'kinds' of types.
//!
//! Rust types can be classified in various useful ways according to
//! intrinsic properties of the type. These classifications, often called
//! 'kinds', are represented as traits.
//!
//! They cannot be implemented by user code, but are instead implemented
//! by the compiler automatically for the types to which they apply.
//!
//! Marker types are special types that are used with unsafe code to
//! inform the compiler of special constraints. Marker types should
//! only be needed when you are creating an abstraction that is
//! implemented using unsafe code. In that case, you may want to embed
//! some of the marker types below into your type.

#![stable]

use clone::Clone;
use cmp;
use option::Option;
use hash::{Hash, Hasher};

/// Types able to be transferred across task boundaries.
#[unstable = "will be overhauled with new lifetime rules; see RFC 458"]
#[lang="send"]
pub unsafe trait Send: 'static + MarkerTrait {
    // empty.
}

/// Types with a constant size known at compile-time.
#[stable]
#[lang="sized"]
pub trait Sized : MarkerTrait {
    // Empty.
}

/// Types that can be copied by simply copying bits (i.e. `memcpy`).
#[stable]
#[lang="copy"]
pub trait Copy : MarkerTrait {
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
/// (from `std::marker`) to ensure that the compiler doesn't
/// consider the user-defined type to be `Sync`.  Any types with
/// interior mutability must also use the `std::cell::UnsafeCell` wrapper
/// around the value(s) which can be mutated when behind a `&`
/// reference; not doing this is undefined behaviour (for example,
/// `transmute`-ing from `&T` to `&mut T` is illegal).
#[unstable = "will be overhauled with new lifetime rules; see RFC 458"]
#[lang="sync"]
pub unsafe trait Sync : MarkerTrait {
    // Empty
}

/// A type which is considered "not sendable", meaning that it cannot
/// be safely sent between tasks, even if it is owned. This is
/// typically embedded in other types, such as `Gc`, to ensure that
/// their instances remain thread-local.
#[unstable = "likely to change with new variance strategy"]
#[lang="no_send_bound"]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NoSend;

/// A type which is considered "not POD", meaning that it is not
/// implicitly copyable. This is typically embedded in other types to
/// ensure that they are never copied, even if they lack a destructor.
#[unstable = "likely to change with new variance strategy"]
#[lang="no_copy_bound"]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
#[allow(missing_copy_implementations)]
pub struct NoCopy;

/// A type which is considered "not sync", meaning that
/// its contents are not threadsafe, hence they cannot be
/// shared between tasks.
#[unstable = "likely to change with new variance strategy"]
#[lang="no_sync_bound"]
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NoSync;

/// A type which is considered managed by the GC. This is typically
/// embedded in other types.
#[unstable = "likely to change with new variance strategy"]
#[lang="managed_bound"]
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
#[allow(missing_copy_implementations)]
pub struct Managed;

macro_rules! impls{
    ($t: ident) => (
        #[cfg(stage0)]
        impl<T:?Sized, S> Hash<S> for $t<T> {
            #[inline]
            fn hash(&self, _: &mut S) {
            }
        }

        #[cfg(not(stage0))]
        impl<T:?Sized, S: Hasher> Hash<S> for $t<T> {
            #[inline]
            fn hash(&self, _: &mut S) {
            }
        }

        impl<T:?Sized> cmp::PartialEq for $t<T> {
            fn eq(&self, _other: &$t<T>) -> bool {
                true
            }
        }

        impl<T:?Sized> cmp::Eq for $t<T> {
        }

        impl<T:?Sized> cmp::PartialOrd for $t<T> {
            fn partial_cmp(&self, _other: &$t<T>) -> Option<cmp::Ordering> {
                Option::Some(cmp::Ordering::Equal)
            }
        }

        impl<T:?Sized> cmp::Ord for $t<T> {
            fn cmp(&self, _other: &$t<T>) -> cmp::Ordering {
                cmp::Ordering::Equal
            }
        }

        impl<T:?Sized> Copy for $t<T> { }

        impl<T:?Sized> Clone for $t<T> {
            fn clone(&self) -> $t<T> {
                $t
            }
        }
        )
}

/// TODO Document me
pub trait MarkerTrait : PhantomSetter<Self> { }
impl<T:?Sized> MarkerTrait for T { }

/// TODO Document me
#[lang="phantom_getter"]
pub trait PhantomGetter<T:?Sized> { }
impl<T:?Sized, U:?Sized> PhantomGetter<T> for U { }

/// TODO Document me
#[lang="phantom_setter"]
pub trait PhantomSetter<T:?Sized> { }
impl<T:?Sized, U:?Sized> PhantomSetter<T> for U { }

/// TODO Document me
#[cfg(stage0)]
#[lang="covariant_type"] // only relevant to stage0
pub struct PhantomData<T:?Sized>;

/// TODO Document me
#[cfg(not(stage0))]
#[lang="phantom_data"]
pub struct PhantomData<T:?Sized>;

impls! { PhantomData }

