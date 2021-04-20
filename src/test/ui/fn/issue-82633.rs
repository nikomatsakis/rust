#![feature(unboxed_closures)]

trait A {
    fn a()
    where
        Self: Sized;
}

fn foo<F: FnOnce<()>>()
where
    F::Output: A,
{
    F::Output::a()
}

fn main() {
    foo::<fn() -> dyn A>()
}
