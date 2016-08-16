#[derive(Clone)] struct Foo<'a>(&'a u32);
impl Copy for Foo<'static> {}

fn main() {
    let s = 2;
    let a = Foo(&s);
    drop(a);
    drop(a);
}
