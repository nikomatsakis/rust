/*!
 * # Hash-Initialized Table (HIT)
 *
 * This module encapsulates the unsafely implemented part of the
 * robin hood hashtable. They key idea is that we have three arrays:
 * hashes, keys, and values. The keys and values arrays are only
 * initialized if hashes are non-zero. The external interface offered
 * by this module maintains that invariant at all times.
 *
 * The exported interface is based around threading the table pointer
 * around. You start out with a `&Table` or `&mut Table`. You can call
 * `peek()` with either kind of reference to examine the state of a
 * particular bucket. In so doing, you *surrender* your reference to
 * the table and get back a `BucketState` which encapsulates it. This
 * `BucketState` can be either an `EmptyBucket` (indicating a spot in
 * the table that has no key/value) or a `FullBucket` (indicating a
 * spot in the table that has been initialized).
 *
 * By encapsulating the table reference you provided, the
 * `BucketState` is able to prevent you from modifying the table,
 * which ensures that the bucket state remains accurate.  Any further
 * operations you would like to do, such as modifying the state of the
 * bucket, are done on the `BucketState` itself.
 *
 * Operations on the bucket state fall into three categories:
 *
 * 1. *Borrowing operations* like `read()` or `read_mut()` cannot change
 *    the state of a bucket. These operations are defined to borrow
 *    the bucket state itself.
 * 2. *Updating operations* change the state of a bucket (e.g., `EmptyBucket`
 *    offers a `put()` method that will change the bucket from empty to full).
 *    These methods consume a bucket state and return a new one.
 * 3. *Concluding operations* give up the bucket's hold on the table.
 *    For example, `to_table()` consumes the bucket and yields back the
 *    original table reference, and `to_refs()` and `to_mut_refs()`
 *    consume the bucket and yield back pointers into the table.
 *
 * It is important to clarify what invariants the HIT inferface guarantees:
 * - No unininitialized memory will be accessed in any way.
 * - Given a `EmptyBucket`, the corresponding index in the table will
 *   always have a hash of 0 and the entries in the key/value arrays
 *   will be considered uninitialized (and hence cannot be accessed).
 * - Given a `FullBucket`, the corresponding index in the table will
 *   always have a non-zero hash and the entries in the key/value arrays
 *   will thus be initialized to valid keys/values.
 *
 * The HIT *DOES NOT* make any kind of extended guarantees about the placement
 * of keys and values:
 * - In particular, no guarantee is made that the hash of a key is equal
 *   to the hash in the hash array, or that the index of a key correctly
 *   corresponds with its hash. Ensuring such things is the job of
 *   the user of the HIT (a Robin Hood hash, in particular, has rather stringent
 *   invariants it must maintain.)
 */

extern crate libc;
use std::intrinsics::{transmute, move_val_init};
use std::mem::{size_of, pref_align_of};
use std::ptr;
use std::rt::heap;
use std::iter::{range_step_inclusive};

pub struct Table<K,V> {
    capacity: uint,
    size: uint,
    hashes: *mut u64,
    keys: *mut K,
    values: *mut V,
}

pub enum BucketState<M> {
    EmptyBucket(EmptyBucket<M>),
    FullBucket(FullBucket<M>),
}

pub trait Bucket<M> {
    fn table<'a>(&'a self) -> &'a M;
    fn to_table(self) -> M;
    fn index(&self) -> uint;
}

pub struct EmptyBucket<M> {
    table: M,
    index: uint,
}

pub struct FullBucket<M> {
    table: M,
    index: uint,
    hash: SafeHash,
}

/**
 * A Gap represents the state of two buckets at once. The first bucket
 * is known to be empty, and the second bucket may be empty or may not
 * be. See `GapState` as the means to test that. You can construct a
 * `Gap` by invoking `peek_gap()` on an empty bucket.
 */
pub struct Gap<B> {
    /** Index of the gap (known to be empty) */
    gap: uint,

    /** State of the second bucket (maybe empty, maybe not) */
    bucket: B
}

pub enum GapState<M> {
    GapThenEmpty(Gap<EmptyBucket<M>>),
    GapThenFull(Gap<FullBucket<M>>),
}

///////////////////////////////////////////////////////////////////////////
// TableRef

/**
 * This trait encapsulates over `&Table` and `&mut Table` references.
 * It is essentially a workaround for the fact that we cannot write
 * code that is generic over mutability.
 */
pub trait TableRef<K,V> {
    fn size(&self) -> uint {
        self.borrow().size
    }

    fn capacity(&self) -> uint {
        self.borrow().capacity
    }

    fn hash(&self, index: uint) -> u64 {
        assert!(index < self.capacity());
        unsafe {
            *self.borrow().hashes.offset(index as int)
        }
    }

    fn borrow<'a>(&'a self) -> &'a Table<K,V>;
}

impl<'table,K,V> TableRef<K,V> for &'table Table<K,V> {
    fn borrow<'a>(&'a self) -> &'a Table<K,V> {
        &**self
    }
}

impl<'table,K,V> TableRef<K,V> for &'table mut Table<K,V> {
    fn borrow<'a>(&'a self) -> &'a Table<K,V> {
        &**self
    }
}

//////////////////////////////////////////////////////////////////////////

/// A hash that is not zero, since we use that to represent empty buckets.
#[deriving(Eq)]
pub struct SafeHash {
    hash: u64,
}

static EMPTY_BUCKET: u64 = 0u64;

impl SafeHash {
    pub fn new(unsafe_hash: u64) -> SafeHash {
        if unsafe_hash == EMPTY_BUCKET {
            SafeHash { hash: unsafe_hash | 0x8000_0000_0000_0000_u64 }
        } else {
            SafeHash { hash: unsafe_hash }
        }
    }

    /// Peek at the hash value, which is guaranteed to be non-zero.
    pub fn to_u64(&self) -> u64 { self.hash }
}

//////////////////////////////////////////////////////////////////////////

pub type EmptyBucketImm<'table,K,V> = EmptyBucket<&'table Table<K,V>>;
pub type FullBucketImm<'table,K,V> = FullBucket<&'table Table<K,V>>;
pub type EmptyBucketMut<'table,K,V> = EmptyBucket<&'table mut Table<K,V>>;
pub type FullBucketMut<'table,K,V> = FullBucket<&'table mut Table<K,V>>;

impl<K,V,M:TableRef<K,V>> EmptyBucket<M> {
    pub fn peek_gap(self, next_index: uint) -> GapState<M> {
        let index = self.index;
        let table = self.to_table();
        match table.peek(next_index) {
            EmptyBucket(eb) => GapThenEmpty(Gap { gap: index, bucket: eb }),
            FullBucket(fb) => GapThenFull(Gap { gap: index, bucket: fb }),
        }
    }
}

impl<K,V,M:TableRef<K,V>> FullBucket<M> {
    pub fn hash(&self) -> SafeHash {
        self.hash
    }
}

impl<M> Bucket<M> for EmptyBucket<M> {
    fn table<'a>(&'a self) -> &'a M {
        &self.table
    }

    fn to_table(self) -> M {
        self.table
    }

    fn index(&self) -> uint {
        self.index
    }
}

impl<M> Bucket<M> for FullBucket<M> {
    fn table<'a>(&'a self) -> &'a M {
        &self.table
    }

    fn to_table(self) -> M {
        self.table
    }

    fn index(&self) -> uint {
        self.index
    }
}

//////////////////////////////////////////////////////////////////////////
// A Gap represents the state of two buckets at once. The first bucket,
// called the gap, is known to be empty. The second bucket, stored
// in the field `bucket`, may be empty or full.

impl<B> Gap<B> {
    pub fn bucket<'a>(&'a self) -> &'a B {
        &self.bucket
    }
}

impl<'a,K,V> Gap<FullBucket<&'a mut Table<K,V>>> {
    pub fn shift(self) -> EmptyBucket<&'a mut Table<K,V>> {
        let old_gap = self.gap;
        let hash = self.bucket.hash;
        let (new_gap, k, v) = self.bucket.take();
        new_gap.table.put(old_gap, hash, k, v);
        new_gap
    }
}

///////////////////////////////////////////////////////////////////////////
// Operations on the table

impl<K,V> Table<K,V> {
    /// Does not initialize the buckets. The caller should ensure they,
    /// at the very least, set every hash to EMPTY_BUCKET.
    unsafe fn new_uninitialized(capacity: uint) -> Table<K, V> {
        let hashes_size =
            capacity.checked_mul(&size_of::<u64>()).expect("capacity overflow");
        let keys_size   =
            capacity.checked_mul(&size_of::< K >()).expect("capacity overflow");
        let vals_size   =
            capacity.checked_mul(&size_of::< V >()).expect("capacity overflow");

        /*
        The following code was my first pass at making RawTable only
        allocate a single buffer, since that's all it needs. There's
        no logical reason for this to require three calls to malloc.

        However, I'm not convinced the code below is correct. If you
        want to take a stab at it, please do! The alignment is
        especially tricky to get right, especially if you need more
        alignment than malloc guarantees.

        let hashes_offset = 0;
        let keys_offset   = align_size(hashes_offset + hashes_size, keys_align);
        let vals_offset   = align_size(keys_offset + keys_size, vals_align);
        let end = vals_offset + vals_size;

        let buffer = global_heap::malloc_raw(end);

        let hashes = buffer.offset(hashes_offset) as *mut u64;
        let keys   = buffer.offset(keys_offset)   as *mut K;
        let vals   = buffer.offset(vals_offset)   as *mut V;

         */

        let align_u64 = pref_align_of::<u64>();
        let align_K = pref_align_of::<K>();
        let align_V = pref_align_of::<V>();
        let hashes = heap::allocate(hashes_size, align_u64) as *mut u64;
        let keys   = heap::allocate(keys_size, align_K) as *mut K;
        let values = heap::allocate(vals_size, align_V) as *mut V;

        Table {
            capacity: capacity,
            size:     0,
            hashes:   hashes,
            keys:     keys,
            values:   values,
        }
    }

    /// Creates a new raw table from a given capacity. All buckets are
    /// initially empty.
    pub fn new(capacity: uint) -> Table<K, V> {
        unsafe {
            let ret = Table::new_uninitialized(capacity);

            for i in range(0, ret.capacity as int) {
                *ret.hashes.offset(i) = EMPTY_BUCKET;
            }

            ret
        }
    }

    pub fn move_iter(self) -> MoveEntries<K, V> {
        MoveEntries { table: self, idx: 0 }
    }

    pub fn size(&self) -> uint {
        self.borrow().size
    }

    pub fn capacity(&self) -> uint {
        self.borrow().capacity
    }

    fn put(&mut self, index: uint, hash: SafeHash, key: K, value: V) {
        /*!
         * Overwrites the entry at `index`, which must be an empty
         * bucket. Note that this function is NOT public -- the public
         * version is exposed on EmptyBucket.
         */

        // Statically guaranteed, only needed in DEBUG builds:
        assert_eq!(self.hash(index), 0);

        let iindex = index as int; // FIXME
        unsafe {
            *self.hashes.offset(iindex) = hash.to_u64();
            move_val_init(&mut *self.keys.offset(iindex), key);
            move_val_init(&mut *self.values.offset(iindex), value);
        }
        self.size += 1;
    }
}

pub trait HitOps {
    /** Examine a given index and yield its current state. */
    fn peek(self, index: uint) -> BucketState<Self>;
}

pub fn peek<K,V,M:TableRef<K,V>>(table: M, index: uint) -> BucketState<M> {
    // FIXME -- I think this fn is needed due to overagressive autoref
    // coupled with overagressive borrowck rules that don't permit loans
    // to be forgotten when reborrowed pointer is mutated
    table.peek(index)
}

impl<K,V,M:TableRef<K,V>> HitOps for M {
    fn peek(self, index: uint) -> BucketState<M> {
        assert!(index < self.capacity());
        let hash = self.hash(index);
        if hash == EMPTY_BUCKET {
            EmptyBucket(EmptyBucket { table: self, index: index })
        } else {
            FullBucket(FullBucket { table: self, index: index,
                                    hash: SafeHash { hash: hash } })
        }
    }
}

#[unsafe_destructor]
impl<K, V> Drop for Table<K, V> {
    fn drop(&mut self) {
        // Ideally, this should be in reverse, since we're likely to have
        // partially taken some elements out with `.move_iter()` from the
        // front.
        for i in range_step_inclusive(self.capacity as int - 1, 0, -1) {
            // Check if the size is 0, so we don't do a useless scan when
            // dropping empty tables such as on resize.

            if self.size == 0 { break }

            match self.peek(i as uint) {
                EmptyBucket(_)  => {},
                FullBucket(fb) => { fb.take(); }
            }
        }

        assert!(self.size == 0);

        let capacity = self.capacity;
        let hashes_size =
            capacity.checked_mul(&size_of::<u64>()).expect("capacity overflow");
        let keys_size   =
            capacity.checked_mul(&size_of::< K >()).expect("capacity overflow");
        let vals_size   =
            capacity.checked_mul(&size_of::< V >()).expect("capacity overflow");
        let align_u64 = pref_align_of::<u64>();
        let align_K = pref_align_of::<K>();
        let align_V = pref_align_of::<V>();

        unsafe {
            heap::deallocate(self.values as *mut u8,
                             hashes_size, align_u64);
            heap::deallocate(self.keys as *mut u8,
                             keys_size, align_K);
            heap::deallocate(self.values as *mut u8,
                             vals_size, align_V);
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// clone() -- this cannot be implemented as efficiently from the outside,
// because we'd have to at least initialize the destination hash array.

impl<K:Clone,V:Clone> Clone for Table<K,V> {
    fn clone(&self) -> Table<K,V> {
        unsafe {
            let mut new_ht = Table::new_uninitialized(self.capacity());

            for i in range(0, self.capacity()) {
                match self.peek(i) {
                    EmptyBucket(_)  => {
                        *new_ht.hashes.offset(i as int) = EMPTY_BUCKET;
                    },
                    FullBucket(fb) => {
                        let hash = fb.hash().to_u64();
                        let (k, v) = fb.read();
                        *new_ht.hashes.offset(i as int) = hash;
                        move_val_init(&mut *new_ht.keys.offset(i as int), (*k).clone());
                        move_val_init(&mut *new_ht.values.offset(i as int), (*v).clone());
                    }
                }
            }

            new_ht.size = self.size();

            new_ht
        }
    }
}

///////////////////////////////////////////////////////////////////////////
// move_iter() [cannot be implemented safely in an equally efficient way]

pub struct MoveEntries<K, V> {
    table: Table<K, V>,
    idx: uint,
}

impl<K, V> Iterator<(SafeHash, K, V)> for MoveEntries<K, V> {
    fn next(&mut self) -> Option<(SafeHash, K, V)> {
        while self.idx < self.table.capacity {
            let i = self.idx;
            self.idx += 1;

            match peek(&mut self.table, i) {
                EmptyBucket(_) => {},
                FullBucket(b) => {
                    let h = b.hash;
                    let (_, k, v) = b.take();
                    return Some((h, k, v));
                }
            }
        }

        None
    }

    fn size_hint(&self) -> (uint, Option<uint>) {
        let size = self.table.size;
        (size, Some(size))
    }
}

///////////////////////////////////////////////////////////////////////////
// Operations on buckets

impl<'table,K,V> EmptyBucket<&'table mut Table<K,V>> {
    pub fn put(self, hash: SafeHash, key: K, value: V)
               -> FullBucketMut<'table,K,V>
    {
        self.table.put(self.index, hash, key, value);
        FullBucket { index: self.index, hash: hash, table: self.table }
    }
}

impl<'table,K,V> FullBucket<&'table mut Table<K,V>> {
    pub fn read_mut<'a>(&'a mut self)
                        -> (&'a mut SafeHash, &'a mut K, &'a mut V)
    {
        // Abuse the fact that a pointer to any u64 in the
        // hashtable at a full index is a safe hash. Thanks to `SafeHash`
        // just being a wrapper around u64, this is true, and the exposed
        // API is also safe: you can only update the entry to another SafeHash,
        // and thus the self remains full.
        let index = self.index as int; // FIXME
        unsafe {
            (transmute::<*mut u64, &'a mut SafeHash>(
                self.table.hashes.offset(index)),
             &mut *self.table.keys.offset(index),
             &mut *self.table.values.offset(index))
        }
    }

    pub fn take(self) -> (EmptyBucketMut<'table,K,V>, K, V) {
        unsafe {
            let index = self.index as int;
            *self.table.hashes.offset(index) = EMPTY_BUCKET;
            let keys: *K = &*self.table.keys;
            let key = ptr::read(keys.offset(index));
            let values: *V = &*self.table.values;
            let value = ptr::read(values.offset(index));
            self.table.size -= 1;
            (EmptyBucket { index: self.index, table: self.table }, key, value)
        }
    }
}

impl<K,V,M:TableRef<K,V>> FullBucket<M> {
    pub fn read<'a>(&'a self) -> (&'a K, &'a V) {
        unsafe {
            let index = self.index as int; // FIXME
            let table = self.table.borrow();
            (&*table.keys.offset(index),
             &*table.values.offset(index))
        }
    }
}

impl<'table,K,V> FullBucket<&'table Table<K,V>> {
    pub fn to_refs(self) -> (&'table K, &'table V) {
        /*!
         * Exchange a bucket state for immutable references into the
         * table. Because the underlying reference to the table is
         * also consumed, no further changes to the structure of the
         * table are possible; in exchange for this, the returned
         * references have a longer lifetime than the references
         * returned by `read()`.
         */
        unsafe {
            let FullBucket { index, table, .. } = self;
            let index = index as int; // FIXME
            (&*table.keys.offset(index),
             &*table.values.offset(index))
        }
    }
}

impl<'table,K,V> FullBucket<&'table mut Table<K,V>> {
    pub fn to_mut_refs(self) -> (&'table mut K, &'table mut V) {
        /*!
         * Exchange a bucket state for references into the table where
         * the value reference is mutable. Because the underlying
         * reference to the table is also consumed, no further changes
         * to the structure of the table are possible; in exchange for
         * this, the returned references have a longer lifetime than
         * the references returned by `read_mut()`.
         */
        unsafe {
            let FullBucket { index, table, .. } = self;
            let index = index as int; // FIXME
            (&mut *table.keys.offset(index),
             &mut *table.values.offset(index))
        }
    }
}
