#![cfg(test)]

extern crate test;
use self::test::BenchHarness;
use std::iter::{range_inclusive};

#[bench]
fn insert(b: &mut BenchHarness) {
    use super::HashMap;

    let mut m = HashMap::new();

    for i in range_inclusive(1, 1000) {
        m.insert(i, i);
    }

    let mut k = 1001;

    b.iter(|| {
        m.insert(k, k);
        k += 1;
    });
}

#[bench]
fn find_existing(b: &mut BenchHarness) {
    use super::HashMap;

    let mut m = HashMap::new();

    for i in range_inclusive(1, 1000) {
        m.insert(i, i);
    }

    b.iter(|| {
        m.contains_key(&412);
    });
}

#[bench]
fn find_nonexisting(b: &mut BenchHarness) {
    use super::HashMap;

    let mut m = HashMap::new();

    for i in range_inclusive(1, 1000) {
        m.insert(i, i);
    }

    b.iter(|| {
        m.contains_key(&2048);
    });
}

#[bench]
fn hashmap_as_queue(b: &mut BenchHarness) {
    use super::HashMap;

    let mut m = HashMap::new();

    for i in range_inclusive(1, 1000) {
        m.insert(i, i);
    }

    let mut k = 1;

    b.iter(|| {
        m.pop(&k);
        m.insert(k + 1000, k + 1000);
        k += 1;
    });
}

#[bench]
fn find_pop_insert(b: &mut BenchHarness) {
    use super::HashMap;

    let mut m = HashMap::new();

    for i in range_inclusive(1, 1000) {
        m.insert(i, i);
    }

    let mut k = 1;

    b.iter(|| {
        m.find(&(k + 400));
        m.find(&(k + 2000));
        m.pop(&k);
        m.insert(k + 1000, k + 1000);
        k += 1;
    })
}
