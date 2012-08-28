struct X { x: (); drop { error!("destructor runs"); } }

fn main() {
    let x = some((X { x: () }, X { x: () }));
    match move x {
        some((move _y, ref _z)) => { }, //~ ERROR cannot bind by-move and by-ref in the same pattern
        none => fail
    }
}
