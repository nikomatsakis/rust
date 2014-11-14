// A zero-dependency test that covers some basic traits, default
// methods, etc.  When mucking about with basic type system stuff I
// often encounter problems in the iterator trait, so it's useful to
// have hanging around. -nmatsakis

// error-pattern: requires `start` lang_item

#![no_std]
#![feature(lang_items)]

#[lang = "sized"]
pub trait Sized for Sized? {
    // Empty.
}

#[unstable = "Definition may change slightly after trait reform"]
pub trait PartialEq for Sized? {
    /// This method tests for `self` and `other` values to be equal, and is used by `==`.
    fn eq(&self, other: &Self) -> bool;
}

#[cfg(not(stage0))]  // NOTE(stage0): remove cfg after a snapshot
#[unstable = "Trait is unstable."]
impl<'a, Sized? T: PartialEq> PartialEq for &'a T {
    #[inline]
    fn eq(&self, other: & &'a T) -> bool { PartialEq::eq(*self, *other) }
}

fn main() { }
