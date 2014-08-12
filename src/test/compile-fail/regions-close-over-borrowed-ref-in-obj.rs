trait Foo { }

impl<'a> Foo for &'a int { }

fn main() {
    let blah;
    {
        let ss: &int = &1; //~ ERROR borrowed value does not live long enough
        blah = box ss as Box<Foo>;
    }
}
