/*!
 * HashSet -- a simple set based around the HashMap interface.
 */

use super::Entries;
use super::MoveEntries;
use super::HashMap;
use super::INITIAL_CAPACITY;
use std::default::Default;
use std::fmt;
use std::fmt::Show;
use std::iter;
use std::iter::{FilterMap, Chain, Repeat, Zip};
use std::hash::{Hash, Hasher, sip};

mod test;

/// HashSet iterator
pub type SetItems<'a, K> =
    iter::Map<'static, (&'a K, &'a ()), &'a K, Entries<'a, K, ()>>;

/// HashSet move iterator
pub type SetMoveItems<K> =
    iter::Map<'static, (K, ()), K, MoveEntries<K, ()>>;

/// An implementation of a hash set using the underlying representation of a
/// HashMap where the value is (). As with the `HashMap` type, a `HashSet`
/// requires that the elements implement the `Eq` and `Hash` traits.
#[deriving(Clone)]
pub struct HashSet<T, H = sip::SipHasher> {
    map: HashMap<T, (), H>
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S>> Eq for HashSet<T, H> {
    // FIXME #11998: Since the value is a (), and `find` returns a Some(&()),
    // we trigger #11998 when matching on it. I've fallen back to manual
    // iteration until this is fixed.
    fn eq(&self, other: &HashSet<T, H>) -> bool {
        if self.len() != other.len() { return false; }

        self.iter().all(|key| other.map.contains_key(key))
    }
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S>> Container for HashSet<T, H> {
    /// Return the number of elements in the set
    fn len(&self) -> uint { self.map.len() }
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S>> Mutable for HashSet<T, H> {
    /// Clear the set, removing all values.
    fn clear(&mut self) { self.map.clear() }
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S>> Set<T> for HashSet<T, H> {
    /// Return true if the set contains a value
    fn contains(&self, value: &T) -> bool { self.map.contains_key(value) }

    /// Return true if the set has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    fn is_disjoint(&self, other: &HashSet<T, H>) -> bool {
        self.iter().all(|v| !other.contains(v))
    }

    /// Return true if the set is a subset of another
    fn is_subset(&self, other: &HashSet<T, H>) -> bool {
        self.iter().all(|v| other.contains(v))
    }

    /// Return true if the set is a superset of another
    fn is_superset(&self, other: &HashSet<T, H>) -> bool {
        other.is_subset(self)
    }
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S>> MutableSet<T> for HashSet<T, H> {
    /// Add a value to the set. Return true if the value was not already
    /// present in the set.
    fn insert(&mut self, value: T) -> bool { self.map.insert(value, ()) }

    /// Remove a value from the set. Return true if the value was
    /// present in the set.
    fn remove(&mut self, value: &T) -> bool { self.map.remove(value) }
}

impl<T: Hash + TotalEq> HashSet<T, sip::SipHasher> {
    /// Create an empty HashSet
    pub fn new() -> HashSet<T, sip::SipHasher> {
        HashSet::with_capacity(INITIAL_CAPACITY)
    }

    /// Create an empty HashSet with space for at least `n` elements in
    /// the hash table.
    pub fn with_capacity(capacity: uint) -> HashSet<T, sip::SipHasher> {
        HashSet { map: HashMap::with_capacity(capacity) }
    }
}

impl<T:TotalEq+Hash<S>,S,H:Hasher<S>> HashSet<T, H> {
    pub fn with_hasher(hasher: H) -> HashSet<T, H> {
        HashSet::with_capacity_and_hasher(INITIAL_CAPACITY, hasher)
    }

    /// Create an empty HashSet with space for at least `capacity`
    /// elements in the hash table, using `hasher` to hash the keys.
    ///
    /// Warning: `hasher` is normally randomly generated, and
    /// is designed to allow `HashSet`s to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    pub fn with_capacity_and_hasher(capacity: uint, hasher: H) -> HashSet<T, H> {
        HashSet { map: HashMap::with_capacity_and_hasher(capacity, hasher) }
    }

    /// Reserve space for at least `n` elements in the hash table.
    pub fn reserve(&mut self, n: uint) {
        self.map.reserve(n)
    }

    /// Returns true if the hash set contains a value equivalent to the
    /// given query value.
    pub fn contains_equiv<Q: Hash<S> + Equiv<T>>(&self, value: &Q) -> bool {
      self.map.contains_key_equiv(value)
    }

    /// An iterator visiting all elements in arbitrary order.
    /// Iterator element type is &'a T.
    pub fn iter<'a>(&'a self) -> SetItems<'a, T> {
        self.map.keys()
    }

    /// Creates a consuming iterator, that is, one that moves each value out
    /// of the set in arbitrary order. The set cannot be used after calling
    /// this.
    pub fn move_iter(self) -> SetMoveItems<T> {
        self.map.move_iter().map(|(k, _)| k)
    }

    /// Visit the values representing the difference
    pub fn difference<'a>(&'a self, other: &'a HashSet<T, H>) -> SetAlgebraItems<'a, T, H> {
        Repeat::new(other)
            .zip(self.iter())
            .filter_map(|(other, elt)| {
                if !other.contains(elt) { Some(elt) } else { None }
            })
    }

    /// Visit the values representing the symmetric difference
    pub fn symmetric_difference<'a>(&'a self, other: &'a HashSet<T, H>)
        -> Chain<SetAlgebraItems<'a, T, H>, SetAlgebraItems<'a, T, H>> {
        self.difference(other).chain(other.difference(self))
    }

    /// Visit the values representing the intersection
    pub fn intersection<'a>(&'a self, other: &'a HashSet<T, H>)
        -> SetAlgebraItems<'a, T, H> {
        Repeat::new(other)
            .zip(self.iter())
            .filter_map(|(other, elt)| {
                if other.contains(elt) { Some(elt) } else { None }
            })
    }

    /// Visit the values representing the union
    pub fn union<'a>(&'a self, other: &'a HashSet<T, H>)
        -> Chain<SetItems<'a, T>, SetAlgebraItems<'a, T, H>> {
        self.iter().chain(other.difference(self))
    }

}

impl<T: TotalEq + Hash<S> + fmt::Show, S, H: Hasher<S>> fmt::Show for HashSet<T, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f.buf, r"\{"));

        for (i, x) in self.iter().enumerate() {
            if i != 0 { try!(write!(f.buf, ", ")); }
            try!(write!(f.buf, "{}", *x));
        }

        write!(f.buf, r"\}")
    }
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S> + Default> FromIterator<T> for HashSet<T, H> {
    fn from_iter<I: Iterator<T>>(iter: I) -> HashSet<T, H> {
        let (lower, _) = iter.size_hint();
        let mut set = HashSet::with_capacity_and_hasher(lower, Default::default());
        set.extend(iter);
        set
    }
}

impl<T: TotalEq + Hash<S>, S, H: Hasher<S> + Default> Extendable<T> for HashSet<T, H> {
    fn extend<I: Iterator<T>>(&mut self, mut iter: I) {
        for k in iter {
            self.insert(k);
        }
    }
}

impl<T: TotalEq + Hash> Default for HashSet<T, sip::SipHasher> {
    fn default() -> HashSet<T> { HashSet::new() }
}

// `Repeat` is used to feed the filter closure an explicit capture
// of a reference to the other set
/// Set operations iterator
pub type SetAlgebraItems<'a, T, H> =
    FilterMap<'static, (&'a HashSet<T, H>, &'a T), &'a T,
              Zip<Repeat<&'a HashSet<T, H>>, SetItems<'a, T>>>;
