// check-pass

mod defining_scope {
    trait Trait {
        type Assoc;
    }

    impl Trait for () {
        type Assoc = ();
    }

    pub fn unit() -> impl Into<<() as Trait>::Assoc> {}
}
use defining_scope::*;

pub fn ice() {
    Into::into(unit());
}

fn main() {}
