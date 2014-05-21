/*!
 * HashMap -- a robin hood hashing algorithm based around a HIT.
 */

extern crate rand;
use super::hit;
use super::hit::{SafeHash,Bucket,Table,EmptyBucket,FullBucket,
                 FullBucketMut,FullBucketImm,
                 HitOps,BucketState,GapThenEmpty,GapThenFull};
use super::hit::TableRef;
use std::cmp::{Eq, TotalEq, Equiv, max};
use std::default::Default;
use std::hash::{Hash, Hasher, sip};
use std::iter;
use std::iter::{range, range_inclusive};
use std::fmt;
use std::fmt::Show;
use std::mem::replace;
use std::num;
use rand::Rng;

mod test;

#[deriving(Clone)]
pub struct HashMap<K, V, H = sip::SipHasher> {
    // All hashes are keyed on these values, to prevent hash collision attacks.
    hasher: H,

    // When size == grow_at, we double the capacity.
    grow_at: uint,

    // The capacity must never drop below this.
    minimum_capacity: uint,

    table: Table<K, V>,

    // We keep this at the end since it's 4-bytes, unlike everything else
    // in this struct. Might as well save a word of padding!
    load_factor: Fraction,
}

// We use this type for the load factor, to avoid floating point operations
// which might not be supported efficiently on some hardware.
//
// We use small u16s here to save space in the hashtable. They get upcasted
// to u64s when we actually use them.
type Fraction = (u16, u16); // (numerator, denominator)

/// HashMap move iterator
pub type MoveEntries<K, V> =
    iter::Map<'static, (SafeHash, K, V), (K, V), hit::MoveEntries<K, V>>;

/// HashMap keys iterator
pub type Keys<'a, K, V> =
    iter::Map<'static, (&'a K, &'a V), &'a K, Entries<'a, K, V>>;

/// HashMap values iterator
pub type Values<'a, K, V> =
    iter::Map<'static, (&'a K, &'a V), &'a V, Entries<'a, K, V>>;

// multiplication by a fraction, in a way that won't generally overflow for
// array sizes outside a factor of 10 of U64_MAX.
fn fraction_mul(lhs: uint, (num, den): Fraction) -> uint {
    (((lhs as u64) * (num as u64)) / (den as u64)) as uint
}

/// Get the number of elements which will force the capacity to grow.
fn grow_at(capacity: uint, load_factor: Fraction) -> uint {
    fraction_mul(capacity, load_factor)
}

static INITIAL_LOG2_CAP: uint = 5;
pub static INITIAL_CAPACITY: uint = 1 << INITIAL_LOG2_CAP; // 2^5
static INITIAL_LOAD_FACTOR: Fraction = (9, 10);

impl<K: Hash + TotalEq, V> HashMap<K, V, sip::SipHasher> {
    /// Create an empty HashMap.
    pub fn new() -> HashMap<K, V, sip::SipHasher> {
        HashMap::with_capacity(INITIAL_CAPACITY)
    }

    pub fn with_capacity(capacity: uint) -> HashMap<K, V, sip::SipHasher> {
        let mut r = rand::task_rng();
        let r0 = r.gen();
        let r1 = r.gen();
        let hasher = sip::SipHasher::new_with_keys(r0, r1);
        HashMap::with_capacity_and_hasher(capacity, hasher)
    }
}

impl<K: TotalEq + Hash<S>, V, S, H: Hasher<S>> HashMap<K, V, H> {
    pub fn with_hasher(hasher: H) -> HashMap<K, V, H> {
        HashMap::with_capacity_and_hasher(INITIAL_CAPACITY, hasher)
    }

    /// Create an empty HashMap with space for at least `capacity`
    /// elements, using `hasher` to hash the keys.
    ///
    /// Warning: `hasher` is normally randomly generated, and
    /// is designed to allow HashMaps to be resistant to attacks that
    /// cause many collisions and very poor performance. Setting it
    /// manually using this function can expose a DoS attack vector.
    pub fn with_capacity_and_hasher(capacity: uint, hasher: H) -> HashMap<K, V, H> {
        let cap = num::next_power_of_two(max(INITIAL_CAPACITY, capacity));
        HashMap {
            hasher:           hasher,
            load_factor:      INITIAL_LOAD_FACTOR,
            grow_at:          grow_at(cap, INITIAL_LOAD_FACTOR),
            minimum_capacity: cap,
            table:            Table::new(cap),
        }
    }

    /// The hashtable will never try to shrink below this size. You can use
    /// this function to reduce reallocations if your hashtable frequently
    /// grows and shrinks by large amounts.
    ///
    /// This function has no effect on the operational semantics of the
    /// hashtable, only on performance.
    pub fn reserve(&mut self, new_minimum_capacity: uint) {
        let cap = num::next_power_of_two(
            max(INITIAL_CAPACITY, new_minimum_capacity));

        self.minimum_capacity = cap;

        if self.table.capacity() < cap {
            self.resize(cap);
        }
    }

    /// Resizes the internal vectors to a new capacity. It's your responsibility to:
    ///   1) Make sure the new capacity is enough for all the elements, accounting
    ///      for the load factor.
    ///   2) Ensure new_capacity is a power of two.
    fn resize(&mut self, new_capacity: uint) {
        assert!(self.table.size() <= new_capacity);
        assert!((new_capacity - 1) & new_capacity == 0);

        self.grow_at = grow_at(new_capacity, self.load_factor);

        let old_table = replace(&mut self.table, Table::new(new_capacity));
        let old_size  = old_table.size();

        for (h, k, v) in old_table.move_iter() {
            swap(&mut self.table, h, k, v);
        }

        assert_eq!(self.table.size(), old_size);
    }

    /// Get the number of elements which will force the capacity to shrink.
    /// When size == self.shrink_at(), we halve the capacity.
    fn shrink_at(&self) -> uint {
        self.table.capacity() >> 2
    }

    /// Performs any necessary resize operations, such that there's space for
    /// new_size elements.
    fn make_some_room(&mut self, new_size: uint) {
        let should_shrink = new_size <= self.shrink_at();
        let should_grow   = self.grow_at <= new_size;

        if should_grow {
            let new_capacity = self.table.capacity() << 1;
            self.resize(new_capacity);
        } else if should_shrink {
            let new_capacity = self.table.capacity() >> 1;

            // Never shrink below the minimum capacity
            if self.minimum_capacity <= new_capacity {
                self.resize(new_capacity);
            }
        }
    }

    fn make_some_room_for_potential_insert(&mut self) {
        let potential_new_size = self.table.size() + 1;
        self.make_some_room(potential_new_size)
    }

    fn make_hash<X: Hash<S>>(&self, x: &X) -> SafeHash {
        SafeHash::new(self.hasher.hash(x))
    }

    /// Search for a key, yielding the index if it's found in the hashtable.
    /// If you already have the hash for the key lying around, use
    /// search_hashed.
    fn search<'a>(&'a self, k: &K) -> Option<FullBucketImm<'a,K,V>> {
        let hash = self.make_hash(k);
        search_hashed(&self.table, hash, k).to_found()
    }

    fn search_equiv<'a,Q:Hash<S>+Equiv<K>>(&'a self,
                                           q: &Q)
                                           -> Option<FullBucketImm<'a,K,V>>
    {
        search_hashed_generic(&self.table, self.make_hash(q), |k| q.equiv(k))
            .to_found()
    }

    fn search_mut_equiv<'a,Q:Hash<S>+Equiv<K>>(&'a mut self,
                                               q: &Q)
                                               -> Option<FullBucketMut<'a,K,V>>
    {
        let hash = self.make_hash(q);
        search_hashed_generic(&mut self.table, hash, |k| q.equiv(k))
            .to_found()
    }

    /// Search for a key, yielding the index if it's found in the hashtable.
    /// If you already have the hash for the key lying around, use
    /// search_hashed.
    fn search_mut<'a>(&'a mut self, k: &K) -> Option<FullBucketMut<'a,K,V>> {
        let hash = self.make_hash(k);
        search_hashed(&mut self.table, hash, k)
            .to_found()
    }

    /// Like `pop`, but can operate on any type that is equivalent to a key.
    #[experimental]
    pub fn pop_equiv<Q:Hash<S> + Equiv<K>>(&mut self, k: &Q) -> Option<V> {
        if self.table.size() == 0 {
            return None
        }

        let potential_new_size = self.table.size() - 1;
        self.make_some_room(potential_new_size);

        let starting_bucket = match self.search_mut_equiv(k) {
            Some(fb) => fb,
            None      => return None,
        };

        pop_internal(starting_bucket)
    }

    /// Return the value corresponding to the key in the map, or create,
    /// insert, and return a new value if it doesn't exist.
    pub fn find_or_insert_with<'a>(&'a mut self, k: K, f: |&K| -> V)
                               -> &'a mut V
    {
        self.make_some_room_for_potential_insert();
        let hash = self.make_hash(&k);
        let fb = match search_hashed_generic(&mut self.table, hash,
                                             |k1| k == *k1) {
            SearchFoundExisting(fb) => {
                fb
            }

            SearchFoundEmpty(eb) => {
                let v = f(&k);
                eb.put(hash, k, v)
            }

            SearchFoundVictim(probe_dib, fb) => {
                let v = f(&k);
                robin_hood(fb, probe_dib, hash, k, v)
            }

            SearchReachedCapacity => {
                fail!("Table reached 100% capacity, this should never happen");
            }
        };
        fb.to_mut_refs().val1()
    }

    /// Insert a key-value pair into the map if the key is not already present.
    /// Otherwise, modify the existing value for the key.
    /// Returns the new or modified value for the key.
    pub fn insert_or_update_with<'a>(
                                 &'a mut self,
                                 k: K,
                                 v: V,
                                 f: |&K, &mut V|)
                                 -> &'a mut V {
        self.make_some_room_for_potential_insert();
        let hash = self.make_hash(&k);
        match search_hashed_generic(&mut self.table, hash,
                                             |k1| k == *k1) {
            SearchFoundExisting(fb) => {
                let r = fb.to_mut_refs().val1();
                f(&k, r);
                r
            }

            SearchFoundEmpty(eb) => {
                eb.put(hash, k, v).to_mut_refs().val1()
            }

            SearchFoundVictim(probe_dib, fb) => {
                robin_hood(fb, probe_dib, hash, k, v).to_mut_refs().val1()
            }

            SearchReachedCapacity => {
                fail!("Table reached 100% capacity, this should never happen");
            }
        }
    }

    /// Retrieves a value for the given key, failing if the key is not present.
    pub fn get<'a>(&'a self, k: &K) -> &'a V {
        match self.find(k) {
            Some(v) => v,
            None => fail!("No entry found for key: {:?}", k)
        }
    }

    /// Retrieves a (mutable) value for the given key, failing if the key is not present.
    pub fn get_mut<'a>(&'a mut self, k: &K) -> &'a mut V {
        match self.find_mut(k) {
            Some(v) => v,
            None => fail!("No entry found for key: {:?}", k)
        }
    }

    /// Return true if the map contains a value for the specified key,
    /// using equivalence.
    pub fn contains_key_equiv<Q: Hash<S> + Equiv<K>>(&self, key: &Q) -> bool {
        self.search_equiv(key).is_some()
    }

    /// Return the value corresponding to the key in the map, using
    /// equivalence.
    pub fn find_equiv<'a, Q:Hash<S>+Equiv<K>>(&'a self, k: &Q) -> Option<&'a V> {
        match self.search_equiv(k) {
            None => None,
            Some(fb) => {
                Some(fb.to_refs().val1())
            }
        }
    }

    /// An iterator visiting all keys in arbitrary order.
    /// Iterator element type is &'a K.
    pub fn keys<'a>(&'a self) -> Keys<'a, K, V> {
        self.iter().map(|(k, _v)| k)
    }

    /// An iterator visiting all values in arbitrary order.
    /// Iterator element type is &'a V.
    pub fn values<'a>(&'a self) -> Values<'a, K, V> {
        self.iter().map(|(_k, v)| v)
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// Iterator element type is (&'a K, &'a V).
    pub fn iter<'a>(&'a self) -> Entries<'a, K, V> {
        Entries { table: &self.table, index: 0 }
    }

    /// Creates a consuming iterator, that is, one that moves each key-value
    /// pair out of the map in arbitrary order. The map cannot be used after
    /// calling this.
    pub fn move_iter(self) -> MoveEntries<K, V> {
        self.table.move_iter().map(|(_, k, v)| (k, v))
    }
}

impl<K: TotalEq + Hash<S>, V: Clone, S, H: Hasher<S>> HashMap<K, V, H> {
    /// Like `find`, but returns a copy of the value.
    pub fn find_copy(&self, k: &K) -> Option<V> {
        self.find(k).map(|v| (*v).clone())
    }

    /// Like `get`, but returns a copy of the value.
    pub fn get_copy(&self, k: &K) -> V {
        (*self.get(k)).clone()
    }
}

impl<K: TotalEq + Hash<S>, V, S, H: Hasher<S>> Container for HashMap<K, V, H> {
    /// Return the number of elements in the map
    fn len(&self) -> uint { self.table.size() }
}

impl<K: TotalEq + Hash<S>, V, S, H: Hasher<S>> Mutable for HashMap<K, V, H> {
    /// Clear the map, removing all key-value pairs.
    fn clear(&mut self) {
        self.minimum_capacity = self.table.size();

        for i in range(0, self.table.capacity()) {
            match (&mut self.table).peek(i) {
                EmptyBucket(_) => {}
                FullBucket(b) => { b.take(); }
            }
        }
    }
}

impl<K: TotalEq + Hash<S>, V, S, H: Hasher<S>> Map<K, V> for HashMap<K, V, H> {
    fn find<'a>(&'a self, k: &K) -> Option<&'a V> {
        self.search(k).map(|bucket: FullBucketImm<'a,K,V>| {
            let (_, v) = bucket.to_refs();
            v
        })
    }

    fn contains_key(&self, k: &K) -> bool {
        self.search(k).is_some()
    }
}

impl<K: TotalEq + Hash<S>, V, S, H: Hasher<S>> MutableMap<K, V> for HashMap<K, V, H> {
    fn find_mut<'a>(&'a mut self, k: &K) -> Option<&'a mut V> {
        match self.search_mut(k) {
            None => None,
            Some(bucket) => {
                let (_, v) = bucket.to_mut_refs();
                Some(v)
            }
        }
    }

    fn swap(&mut self, k: K, v: V) -> Option<V> {
        self.make_some_room_for_potential_insert();
        let hash = self.make_hash(&k);
        swap(&mut self.table, hash, k, v)
    }

    fn pop(&mut self, k: &K) -> Option<V> {
        if self.table.size() == 0 {
            return None
        }

        let potential_new_size = self.table.size() - 1;
        self.make_some_room(potential_new_size);

        match self.search_mut(k) {
            Some(b) => pop_internal(b),
            None  => None
        }
    }
}

pub struct Entries<'table, K, V> {
    table: &'table Table<K, V>,
    index: uint,
}

impl<'table, K, V> Iterator<(&'table K, &'table V)> for Entries<'table, K, V> {
    fn next(&mut self) -> Option<(&'table K, &'table V)> {
        while self.index < self.table.capacity() {
            let i = self.index;
            self.index += 1;

            match self.table.peek(i) {
                EmptyBucket(_)  => {},
                FullBucket(fb) => return Some(fb.to_refs())
            }
        }

        None
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        let size = self.table.size() - self.index;
        (size, Some(size))
    }
}

impl<K:TotalEq+Hash<S>,V:Eq,S,H:Hasher<S>> Eq for HashMap<K, V, H> {
    fn eq(&self, other: &HashMap<K, V, H>) -> bool {
        if self.len() != other.len() { return false; }

        self.iter().all(|(key, value)| {
            match other.find(key) {
                None    => false,
                Some(v) => *value == *v
            }
        })
    }
}

impl<K:TotalEq+Hash<S>+Show,V:Show,S,H:Hasher<S>> Show for HashMap<K, V, H> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        try!(write!(f.buf, r"\{"));

        for (i, (k, v)) in self.iter().enumerate() {
            if i != 0 { try!(write!(f.buf, ", ")); }
            try!(write!(f.buf, "{}: {}", *k, *v));
        }

        write!(f.buf, r"\}")
    }
}

impl<K:TotalEq+Hash<S>,V,S,H:Hasher<S>+Default> FromIterator<(K, V)> for HashMap<K, V, H> {
    fn from_iter<T:Iterator<(K,V)>>(iter: T) -> HashMap<K, V, H> {
        let (lower, _) = iter.size_hint();
        let mut map = HashMap::with_capacity_and_hasher(lower, Default::default());
        map.extend(iter);
        map
    }
}

impl<K:TotalEq+Hash<S>,V,S,H:Hasher<S>+Default> Extendable<(K, V)> for HashMap<K, V, H> {
    fn extend<T:Iterator<(K,V)>>(&mut self, mut iter: T) {
        for (k, v) in iter {
            self.insert(k, v);
        }
    }
}

//////////////////////////////////////////////////////////////////////////

fn swap_bucket<K,V>(full_bucket: &mut hit::FullBucketMut<K,V>,
                    hash: SafeHash,
                    key: K,
                    value: V)
                    -> (SafeHash, K, V)
{
    let (old_hash_ref, old_key_ref, old_val_ref) = full_bucket.read_mut();

    let old_hash = replace(old_hash_ref, hash);
    let old_key  = replace(old_key_ref,  key);
    let old_val  = replace(old_val_ref,  value);

    (old_hash, old_key, old_val)
}

// Probe the `idx`th bucket for a given hash, returning the index of the
// target bucket.
//
// This exploits the power-of-two size of the hashtable. As long as this
// is always true, we can use a bitmask of cap-1 to do modular arithmetic.
//
// Prefer to use this with increasing values of `idx` rather than repeatedly
// calling `probe_next`. This reduces data-dependencies between loops, which
// can help the optimizer, and certainly won't hurt it. `probe_next` is
// simply for convenience, and is no more efficient than `probe`.
fn probe<K,V,M:TableRef<K,V>>(table: &M, hash: SafeHash, idx: uint) -> uint {
    let hash_mask = table.capacity() - 1;

    // So I heard a rumor that unsigned overflow is safe in rust..
    ((hash.to_u64() as uint) + idx) & hash_mask
}

// Generate the next probe index in a sequence. Prefer to use 'probe'
// by itself, but this can sometimes be useful.
fn next_probe_index<K,V,M:TableRef<K,V>,B:Bucket<M>>(bucket: &B) -> (uint) {
    let probe = bucket.index();
    let table = bucket.table();
    let hash_mask = table.capacity() - 1;
    (probe + 1) & hash_mask
}

// Probes the state of the next bucket in the sequence.
fn probe_next<K,V,M:TableRef<K,V>,B:Bucket<M>>(bucket: B) -> BucketState<M> {
    let index = next_probe_index(&bucket);
    bucket.to_table().peek(index)
}

/// Get the distance of the bucket at the given index that it lies
/// from its 'ideal' location.
///
/// In the cited blog posts above, this is called the "distance to
/// inital bucket", or DIB.
fn bucket_distance<K,V,M:TableRef<K,V>>(bucket: &FullBucket<M>) -> uint {
    // where the hash of the element that happens to reside at
    // `index_of_elem` tried to place itself first.
    let first_probe_index = probe(bucket.table(), bucket.hash(), 0);
    let raw_index = bucket.index();
    if first_probe_index <= raw_index {
        // probe just went forward
        raw_index - first_probe_index
    } else {
        // probe wrapped around the hashtable
        raw_index + (bucket.table().capacity() - first_probe_index)
    }
}

fn expect_full<K,V,M:TableRef<K,V>>(table: M, index: uint) -> FullBucket<M> {
    match table.peek(index) {
        FullBucket(b) => b,
        EmptyBucket(..) => {
            fail!("Bucket which should have been full is empty");
        }
    }
}

enum SearchResult<M> {
    // Here is an entry with the given key:
    SearchFoundExisting(FullBucket<M>),

    // There is no entry with the given key, and this empty bucket is
    // where it should go.
    SearchFoundEmpty(EmptyBucket<M>),

    // There is no entry with the given key, and this full bucket is
    // where the key should go. In that case, you'll have to run
    // robin-hood to displace the entry.
    SearchFoundVictim(uint, FullBucket<M>),

    SearchReachedCapacity
}

impl<M> SearchResult<M> {
    fn to_found(self) -> Option<FullBucket<M>> {
        /*!
         * Returns `Some(fb)` if an entry was found (and `fb` is the
         * bucket where it is located. Else `None`.
         */
        match self {
            SearchFoundExisting(fb) => {
                Some(fb)
            }
            SearchFoundEmpty(..) |
            SearchFoundVictim(..) |
            SearchReachedCapacity => {
                None
            }
        }
    }
}

/// Search for a pre-hashed key.
fn search_hashed_generic<K,V,M:TableRef<K,V>>(
    mut table: M,
    hash: SafeHash,
    is_match: |&K| -> bool)
    -> SearchResult<M>
{
    for dib in range_inclusive(0u, table.size()) {
        let probe = probe(&table, hash, dib);

        let full_bucket = match table.peek(probe) {
            EmptyBucket(eb) => {
                return SearchFoundEmpty(eb); // hit an empty bucket
            }
            FullBucket(fb) => fb
        };

        // We can finish the search early if we hit any bucket
        // with a lower distance to initial bucket than we've probed.
        let probe_dib = bucket_distance(&full_bucket);
        if probe_dib < dib {
            return SearchFoundVictim(probe_dib, full_bucket);
        }

        // If the hash doesn't match, it can't be this one.
        if hash != full_bucket.hash() {
            table = full_bucket.to_table();
            continue;
        }

        // If the key doesn't match, it can't be this one.
        let matched = {
            let (k, _) = full_bucket.read();
            is_match(k)
        };
        if !matched {
            table = full_bucket.to_table();
            continue;
        }

        return SearchFoundExisting(full_bucket);
    }

    SearchReachedCapacity
}

fn search_hashed<K:TotalEq,V,M:TableRef<K,V>>(
    table: M,
    hash: SafeHash,
    k: &K)
    -> SearchResult<M>
{
    search_hashed_generic(table, hash, |k_| *k == *k_)
}

fn swap<K:TotalEq,V>(table: &mut Table<K,V>,
                     hash: SafeHash,
                     k: K,
                     v: V)
                     -> Option<V>
{
    match search_hashed_generic(table, hash, |k1| k == *k1) {
        SearchFoundExisting(fb) => {
            let r = fb.to_mut_refs().val1();
            Some(replace(r, v))
        }
        SearchFoundEmpty(eb) => {
            eb.put(hash, k, v);
            None
        }
        SearchFoundVictim(probe_dib, fb) => {
            robin_hood(fb, probe_dib, hash, k, v);
            None
        }
        SearchReachedCapacity => {
            fail!("Table reached 100% capacity, this should never happen");
        }
    }
}

fn pop_internal<K:TotalEq,V>(starting_bucket: FullBucketMut<K,V>)
                             -> Option<V>
{
    // Key idea: If we remove bucket B, then it's possible that the
    // data in bucket (B+1) would have preferred to be in B, in which
    // case we have to shift it down. Moreover, there is a trickle
    // down effect: if we do shift from B+1 to B, then by the same logic
    // the data in B+2 might have preferred to be in B+1.
    //
    // So, in general, we have to continue shifting down until we reach
    // either an empty bucket, or a bucket that is exactly where it wants
    // to be (i.e., the Distance to Ideal Bucket is zero).

    // Empty the initial gap. Remember this return value; we'll want
    // to return it at the end.
    let (mut gap, _, retval) = starting_bucket.take();

    // We'll shift at most size items:
    let size = {
        let table = gap.table(); // FIXME lifetime too short, what?
        table.size()
    };
    for _ in range(0u, size) {
        // Check whether index `gap+1` is occupied by a value that
        // would have preferred to be in index `gap`:
        let next_index = next_probe_index(&gap);
        match gap.peek_gap(next_index) {
            GapThenEmpty(_) => {
                // Bucket after gap is empty. All done.
                break;
            }

            GapThenFull(succ) => {
                // Bucket after gap is full.

                if bucket_distance(succ.bucket()) == 0 {
                    // This data is exactly where it wants to be. All done.
                    break;
                }

                gap = succ.shift();
            }
        }
    }

    // Now we're done all our shifting. Return the value we grabbed
    // earlier.
    return Some(retval);
}

/// Perform robin hood bucket stealing at the given 'full_bucket'. You must
/// also pass that probe's "distance to initial bucket" so we don't have
/// to recalculate it, as well as the total number of probes already done
/// so we have some sort of upper bound on the number of probes to do.
///
/// Returns the safe `FullBucketMut` which was passed in. It will
/// still be full, but it will contain `(k,v)` pair rather than its
/// original contents.
///
/// 'hash', 'k', and 'v' are the elements to robin hood into the hashtable.
fn robin_hood<'a,K:TotalEq,V>(mut full_bucket: FullBucketMut<'a,K,V>,
                              dib_param: uint,
                              hash: SafeHash,
                              k: K,
                              v: V)
                              -> FullBucketMut<'a,K,V>
{
    // Swap (hash, k, v) into `full_bucket`, but now we have to find
    // a new home for the old contents.
    let start_index = full_bucket.index();
    let (old_hash, old_key, old_val) = swap_bucket(&mut full_bucket, hash, k, v);

    let size = {
        let table = full_bucket.table();
        table.size() // FIXME -- failure of region inference, it appears
    };

    for dib in range(dib_param + 1, size) {
        match probe_next(full_bucket) {
            EmptyBucket(b) => {
                // Finally. A hole!
                let b = b.put(old_hash, old_key, old_val);

                // Recover the original bucket. Assert that it is full.
                let table = b.to_table();
                return expect_full(table, start_index);
            }
            FullBucket(b) => {
                full_bucket = b;

                // Robin hood! Steal the spot.
                let probe_dib = bucket_distance(&full_bucket);
                if probe_dib < dib {
                    return robin_hood(full_bucket, probe_dib,
                                      old_hash, old_key, old_val);
                }

                // Otherwise, keep probing.
            }
        }
    }

    fail!("HashMap fatal error: 100% load factor?");
}

