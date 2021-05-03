// run-pass

#![feature(generic_associated_types)]

pub trait Iter {
    type Item<'a> where Self: 'a;

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>>;
}

pub struct Windows<T> {
    t: T,
}

impl<T> Iter for Windows<T> {
    type Item<'a> where T: 'a = &'a mut [T];

    fn next<'a>(&'a mut self) -> Option<Self::Item<'a>> {
        todo!()
    }
}

fn main() {}
