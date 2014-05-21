#![cfg(test)]

use super::HashMap;
use std::cmp::Equiv;
use std::hash::Hash;
use std::iter::{Iterator,range_inclusive,range_step_inclusive};
use std::local_data;
use std::vec;

struct KindaIntLike(int);

impl Equiv<int> for KindaIntLike {
    fn equiv(&self, other: &int) -> bool {
        let KindaIntLike(this) = *self;
        this == *other
    }
}
impl<S: Writer> Hash<S> for KindaIntLike {
    fn hash(&self, state: &mut S) {
        let KindaIntLike(this) = *self;
        this.hash(state)
    }
}

#[test]
fn test_create_capacity_zero() {
    let mut m = HashMap::with_capacity(0);

    assert!(m.insert(1, 1));

    assert!(m.contains_key(&1));
    assert!(!m.contains_key(&0));
}

#[test]
fn test_insert() {
    let mut m = HashMap::new();
    assert_eq!(m.len(), 0);
    assert!(m.insert(1, 2));
    assert_eq!(m.len(), 1);
    assert!(m.insert(2, 4));
    assert_eq!(m.len(), 2);
    assert_eq!(*m.find(&1).unwrap(), 2);
    assert_eq!(*m.find(&2).unwrap(), 4);
}

local_data_key!(drop_vector: vec::Vec<int>)

    #[deriving(Hash, Eq, TotalEq)]
struct Dropable {
    k: uint
}


impl Dropable {
    fn new(k: uint) -> Dropable {
        local_data::get_mut(drop_vector,
                            |v| { v.unwrap().as_mut_slice()[k] += 1; });

        Dropable { k: k }
    }
}

impl Drop for Dropable {
    fn drop(&mut self) {
        local_data::get_mut(drop_vector, |v|
                            { v.unwrap().as_mut_slice()[self.k] -= 1; });
    }
}

#[test]
fn test_drops() {
    local_data::set(drop_vector, vec::Vec::from_elem(200, 0));

    {
        let mut m = HashMap::new();

        local_data::get(drop_vector, |v| {
            for i in range(0u, 200) {
                assert_eq!(v.unwrap().as_slice()[i], 0);
            }
        });

        for i in range(0u, 100) {
            let d1 = Dropable::new(i);
            let d2 = Dropable::new(i+100);
            m.insert(d1, d2);
        }

        local_data::get(drop_vector, |v| {
            for i in range(0u, 200) {
                assert_eq!(v.unwrap().as_slice()[i], 1);
            }
        });

        for i in range(0u, 50) {
            let k = Dropable::new(i);
            let v = m.pop(&k);

            assert!(v.is_some());

            local_data::get(drop_vector, |v| {
                assert_eq!(v.unwrap().as_slice()[i], 1);
                assert_eq!(v.unwrap().as_slice()[i+100], 1);
            });
        }

        local_data::get(drop_vector, |v| {
            for i in range(0u, 50) {
                assert_eq!(v.unwrap().as_slice()[i], 0);
                assert_eq!(v.unwrap().as_slice()[i+100], 0);
            }

            for i in range(50u, 100) {
                assert_eq!(v.unwrap().as_slice()[i], 1);
                assert_eq!(v.unwrap().as_slice()[i+100], 1);
            }
        });
    }

    local_data::get(drop_vector, |v| {
        for i in range(0u, 200) {
            assert_eq!(v.unwrap().as_slice()[i], 0);
        }
    });
}

#[test]
fn test_empty_pop() {
    let mut m: HashMap<int, bool> = HashMap::new();
    assert_eq!(m.pop(&0), None);
}

#[test]
fn test_lots_of_insertions() {
    let mut m = HashMap::new();

    // Try this a few times to make sure we never screw up the hashmap's
    // internal state.
    for _ in range(0, 10) {
        assert!(m.is_empty());

        for i in range_inclusive(1, 1000) {
            assert!(m.insert(i, i));

            for j in range_inclusive(1, i) {
                let r = m.find(&j);
                assert_eq!(r, Some(&j));
            }

            for j in range_inclusive(i+1, 1000) {
                let r = m.find(&j);
                assert_eq!(r, None);
            }
        }

        for i in range_inclusive(1001, 2000) {
            assert!(!m.contains_key(&i));
        }

        // remove forwards
        for i in range_inclusive(1, 1000) {
            assert!(m.remove(&i));

            for j in range_inclusive(1, i) {
                assert!(!m.contains_key(&j));
            }

            for j in range_inclusive(i+1, 1000) {
                assert!(m.contains_key(&j));
            }
        }

        for i in range_inclusive(1, 1000) {
            assert!(!m.contains_key(&i));
        }

        for i in range_inclusive(1, 1000) {
            assert!(m.insert(i, i));
        }

        // remove backwards
        for i in range_step_inclusive(1000, 1, -1) {
            assert!(m.remove(&i));

            for j in range_inclusive(i, 1000) {
                assert!(!m.contains_key(&j));
            }

            for j in range_inclusive(1, i-1) {
                assert!(m.contains_key(&j));
            }
        }
    }
}

#[test]
fn test_find_mut() {
    let mut m = HashMap::new();
    assert!(m.insert(1, 12));
    assert!(m.insert(2, 8));
    assert!(m.insert(5, 14));
    let new = 100;
    match m.find_mut(&5) {
        None => fail!(), Some(x) => *x = new
    }
    assert_eq!(m.find(&5), Some(&new));
}

#[test]
fn test_insert_overwrite() {
    let mut m = HashMap::new();
    assert!(m.insert(1, 2));
    assert_eq!(*m.find(&1).unwrap(), 2);
    assert!(!m.insert(1, 3));
    assert_eq!(*m.find(&1).unwrap(), 3);
}

#[test]
fn test_insert_conflicts() {
    let mut m = HashMap::with_capacity(4);
    assert!(m.insert(1, 2));
    assert!(m.insert(5, 3));
    assert!(m.insert(9, 4));
    assert_eq!(*m.find(&9).unwrap(), 4);
    assert_eq!(*m.find(&5).unwrap(), 3);
    assert_eq!(*m.find(&1).unwrap(), 2);
}

#[test]
fn test_conflict_remove() {
    let mut m = HashMap::with_capacity(4);
    assert!(m.insert(1, 2));
    assert_eq!(*m.find(&1).unwrap(), 2);
    assert!(m.insert(5, 3));
    assert_eq!(*m.find(&1).unwrap(), 2);
    assert_eq!(*m.find(&5).unwrap(), 3);
    assert!(m.insert(9, 4));
    assert_eq!(*m.find(&1).unwrap(), 2);
    assert_eq!(*m.find(&5).unwrap(), 3);
    assert_eq!(*m.find(&9).unwrap(), 4);
    assert!(m.remove(&1));
    assert_eq!(*m.find(&9).unwrap(), 4);
    assert_eq!(*m.find(&5).unwrap(), 3);
}

#[test]
fn test_is_empty() {
    let mut m = HashMap::with_capacity(4);
    assert!(m.insert(1, 2));
    assert!(!m.is_empty());
    assert!(m.remove(&1));
    assert!(m.is_empty());
}

#[test]
fn test_pop() {
    let mut m = HashMap::new();
    m.insert(1, 2);
    assert_eq!(m.pop(&1), Some(2));
    assert_eq!(m.pop(&1), None);
}

#[test]
#[allow(experimental)]
fn test_pop_equiv() {
    let mut m = HashMap::new();
    m.insert(1, 2);
    assert_eq!(m.pop_equiv(&KindaIntLike(1)), Some(2));
    assert_eq!(m.pop_equiv(&KindaIntLike(1)), None);
}

#[test]
fn test_swap() {
    let mut m = HashMap::new();
    assert_eq!(m.swap(1, 2), None);
    assert_eq!(m.swap(1, 3), Some(2));
    assert_eq!(m.swap(1, 4), Some(3));
}

#[test]
fn test_find_or_insert() {
    let mut m = HashMap::new();
    m.insert(1, 2);
    assert_eq!(2, *m.find_or_insert(1, 3));
    assert_eq!(4, *m.find_or_insert(2, 4));
}

#[test]
fn test_find_or_insert_with() {
    let mut m = HashMap::new();
    let mut counter = 3;
    m.insert(1, 2);
    assert_eq!(2, *m.find_or_insert_with(1, || { counter += 1; counter }));
    assert_eq!(4, *m.find_or_insert_with(2, || { counter += 1; counter }));
}

#[test]
fn test_insert_or_update_with() {
    let mut m = HashMap::new();
    let mut counter = 0;
    assert_eq!(2, *m.insert_or_update_with(1, 2, |k, v| {
        fail!("Key not yet present");
    }));
    assert_eq!(3, *m.insert_or_update_with(1, 3, |k, v| {
        counter += 1;
        assert_eq!(*k, 1);
        assert_eq!(*v, 2);
        *v += 1;
    }));
    assert_eq!(counter, 1);
}

#[test]
fn test_move_iter() {
    let hm = {
        let mut hm = HashMap::new();

        hm.insert('a', 1);
        hm.insert('b', 2);

        hm
    };

    let v = hm.move_iter().collect::<Vec<(char, int)>>();
    assert!([('a', 1), ('b', 2)] == v.as_slice() || [('b', 2), ('a', 1)] == v.as_slice());
}

#[test]
fn test_iterate() {
    let mut m = HashMap::with_capacity(4);
    for i in range(0u, 32) {
        assert!(m.insert(i, i*2));
    }
    assert_eq!(m.len(), 32);

    let mut observed: uint = 0;

    for (k, v) in m.iter() {
        assert_eq!(*v, *k * 2);
        observed |= 1 << *k;
    }
    assert_eq!(observed, 0xFFFF_FFFF);
}

#[test]
fn test_keys() {
    let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
    let map = vec.move_iter().collect::<HashMap<int, char>>();
    let keys = map.keys().map(|&k| k).collect::<Vec<int>>();
    assert_eq!(keys.len(), 3);
    assert!(keys.contains(&1));
    assert!(keys.contains(&2));
    assert!(keys.contains(&3));
}

#[test]
fn test_values() {
    let vec = vec![(1, 'a'), (2, 'b'), (3, 'c')];
    let map = vec.move_iter().collect::<HashMap<int, char>>();
    let values = map.values().map(|&v| v).collect::<Vec<char>>();
    assert_eq!(values.len(), 3);
    assert!(values.contains(&'a'));
    assert!(values.contains(&'b'));
    assert!(values.contains(&'c'));
}

#[test]
fn test_find() {
    let mut m = HashMap::new();
    assert!(m.find(&1).is_none());
    m.insert(1, 2);
    match m.find(&1) {
        None => fail!(),
        Some(v) => assert!(*v == 2)
    }
}

#[test]
fn test_eq() {
    let mut m1 = HashMap::new();
    m1.insert(1, 2);
    m1.insert(2, 3);
    m1.insert(3, 4);

    let mut m2 = HashMap::new();
    m2.insert(1, 2);
    m2.insert(2, 3);

    assert!(m1 != m2);

    m2.insert(3, 4);

    assert_eq!(m1, m2);
}

#[test]
fn test_expand() {
    let mut m = HashMap::new();

    assert_eq!(m.len(), 0);
    assert!(m.is_empty());

    let mut i = 0u;
    let old_resize_at = m.grow_at;
    while old_resize_at == m.grow_at {
        m.insert(i, i);
        i += 1;
    }

    assert_eq!(m.len(), i);
    assert!(!m.is_empty());
}

#[test]
fn test_find_equiv() {
    let mut m = HashMap::new();

    let (foo, bar, baz) = (1,2,3);
    m.insert("foo".to_owned(), foo);
    m.insert("bar".to_owned(), bar);
    m.insert("baz".to_owned(), baz);


    assert_eq!(m.find_equiv(&("foo")), Some(&foo));
    assert_eq!(m.find_equiv(&("bar")), Some(&bar));
    assert_eq!(m.find_equiv(&("baz")), Some(&baz));

    assert_eq!(m.find_equiv(&("qux")), None);
}

#[test]
fn test_from_iter() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let map: HashMap<int, int> = xs.iter().map(|&x| x).collect();

    for &(k, v) in xs.iter() {
        assert_eq!(map.find(&k), Some(&v));
    }
}

#[test]
fn test_size_hint() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let map: HashMap<int, int> = xs.iter().map(|&x| x).collect();

    let mut iter = map.iter();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.size_hint(), (3, Some(3)));
}

#[test]
fn test_mut_size_hint() {
    let xs = [(1, 1), (2, 2), (3, 3), (4, 4), (5, 5), (6, 6)];

    let mut map: HashMap<int, int> = xs.iter().map(|&x| x).collect();

    let mut iter = map.mut_iter();

    for _ in iter.by_ref().take(3) {}

    assert_eq!(iter.size_hint(), (3, Some(3)));
}
