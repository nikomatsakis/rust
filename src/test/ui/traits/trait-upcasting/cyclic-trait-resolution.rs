trait A: B + A {}
//~^ ERROR cycle detected when computing the supertraits of `A` [E0391]

trait B {}

impl A for () {}

impl B for () {}

fn main() {
    let a: Box<dyn A> = Box::new(());
    let _b: Box<dyn B> = a;
}
