fn a() -> &int {
    let vec = [1, 2, 3, 4];
    let tail = match vec { //~ ERROR cannot borrow
        [_a, ..tail] => &tail[0],
        _ => fail!(~"foo")
    };
    tail
}

fn main() {
    let fifth = a();
    io::println(fmt!("%d", *fifth));
}
