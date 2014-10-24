trait Get<A,R> {
    fn get(&self, arg: A) -> R;
}

fn foo<T>(t: T)
    where T : for<'a> Get<&'a int, &'a int>
{
}

impl<'a> Get<&'a int, &'a int> for () {
    fn get(&self, arg: &'a int) -> &'a int {
        arg
    }
}

fn main() {
    foo(());
}
