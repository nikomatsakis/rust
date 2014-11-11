// A zero-dependency test that covers some basic traits, default
// methods, etc.  When mucking about with basic type system stuff I
// often encounter problems in the iterator trait, so it's useful to
// have hanging around. -nmatsakis

#![no_std]
#![feature(lang_items)]

#[lang = "sized"]
pub trait Sized for Sized? {
    // Empty.
}

pub mod std {
    pub mod clone {
        pub trait Clone {
            fn clone(&self) -> Self;
        }
    }
}

pub struct ContravariantLifetime<'a>;

impl <'a> ::std::clone::Clone for ContravariantLifetime<'a> {
    #[inline]
    fn clone(&self) -> ContravariantLifetime<'a> {
        match *self { ContravariantLifetime => ContravariantLifetime, }
    }
}

fn main() { }
