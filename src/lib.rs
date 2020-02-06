use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::collections::hash_map::{Drain as MapDrain, Entry, Keys, Values, ValuesMut};
use std::collections::HashMap;
use std::default::Default;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::{FromIterator, FusedIterator};

type IntoIter<K> = ::std::collections::hash_map::IntoIter<K, usize>;
type Iter<'a, K> = ::std::collections::hash_map::Iter<'a, K, usize>;
type IterMut<'a, K> = ::std::collections::hash_map::IterMut<'a, K, usize>;

/// A hash multi set implemented as a `HashMap` where the value is `usize`.
///
/// As with the [`HashMap`] type, a `MultiSet` requires that the elements
/// implement the [`Eq`] and [`Hash`] traits. This can frequently be achieved by
/// using `#[derive(PartialEq, Eq, Hash)]`. If you implement these yourself,
/// it is important that the following property holds:
///
/// ```text
/// k1 == k2 -> hash(k1) == hash(k2)
/// ```
///
/// In other words, if two keys are equal, their hashes must also be equal.
///
///
/// It is a logic error for an item to be modified in such a way that the
/// item's hash, as determined by the [`Hash`] trait, or its equalit, as
/// determined by the [`Eq`] trait, changes while it is in the set. This is
/// normally only possible through [`Cell`], [`RefCell`], global state, I/O, or
/// unsafe code.
///
/// # Examples
///
/// ```text
/// use mset::MultiSet;
///
/// // Ocassionally, type inference will let us omit an explicit type signature
/// // (which would otherwise be `MultiSet<String>` in this example).
/// let mut bag = MultiSet::new();
///
/// // Add some words
/// bag.insert("contemplate".to_string());
/// bag.insert("the".to_string());
/// bag.insert("variations".to_string());
/// bag.insert("of".to_string());
/// bag.insert("the".to_string());
/// bag.insert("23".to_string());
/// bag.insert("letters".to_string());
///
/// // Check for a specific one.
/// if !bag.contains("Hacedor") {
///     println!("We have {} words, but Hacedor ain't one.",
///              bag.len());
/// }
///
/// // Remove a word
/// bag.remove("23");
///
/// // Iterate over everything.
/// for (word, count) in &bag {
///     println!("{}: {}", word, count);
/// }
/// ```
///
/// The easiest way to use `MultiSet` with a custom type is to derive [`Eq`] and
/// [`Hash`]. We must also derive [`PartialEq`], this will in the future be
/// implied by [`Eq`].
///
/// ```text
/// use mset::MultiSet;
/// #[derive(Hash, Eq, PartialEq, Debug)]
/// struct GuineaPig {
///     name: String,
///     weight: usize,
/// }
///
/// let mut gps = MultiSet::new();
///
/// gps.insert(GuineaPig { name: "Mumpkans".to_string(), weight: 8 });
/// gps.insert(GuineaPig { name: "Mumpkans".to_string(), weight: 8 });
/// gps.insert(GuineaPig { name: "Mr. Mister".to_string(), weight: 5 });
/// gps.insert(GuineaPig { name: "Popchop".to_string(), weight: 12 });
/// gps.insert(GuineaPig { name: "Fuzzable".to_string(), weight: 9 });
///
/// // Use derived implementation to print the guinea pigs.
/// for x in &gps {
///     println!("{:?}", x);
/// }
/// ```
///
/// A `MultiSet` with fixed list of elements can be initialized from an array:
///
/// ```text
/// use mset:MultiSet;
///
/// let gps: MultiSet<&'static str> =
///     ["Deathmlom", "Bun Roy", "Funbees", "Sporky", "Bun Roy"].iter().cloned().collect();
/// // use the values stored in the set
/// ```
///
/// [`Cell`]: struct.Cell.html
/// [`Eq`]: trait.Eq.html
/// [`Hash`]: trait.Hash.html
/// [`HashMap`]: struct.HashMap.html
/// [`PartialEq`]: trait.PartialEq.html
/// [`RefCell`]: struct.RefCell.html
#[derive(Clone)]
pub struct MultiSet<K, S = RandomState> {
    elem_counts: HashMap<K, usize, S>,
}

impl<K: Hash + Eq> MultiSet<K, RandomState> {
    /// Create an empty `MultiSet`.
    ///
    /// The multi set is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mset: MultiSet<char> = MultiSet::new();
    /// assert_eq!(mset.len(), 0);
    /// ```
    pub fn new() -> MultiSet<K, RandomState> {
        MultiSet {
            elem_counts: HashMap::new(),
        }
    }

    /// Create an empty `MultiSet` with the specified capacity.
    ///
    /// The multi set will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the multi set will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let mset: MultiSet<i32> = MultiSet::with_capacity(10);
    /// assert!(mset.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> MultiSet<K, RandomState> {
        MultiSet {
            elem_counts: HashMap::with_capacity(capacity),
        }
    }
}

impl<K, S> MultiSet<K, S> {
    /// Returns the number of elements the multi set can hold without reallocating.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mset: MultiSet<i32> = MultiSet::with_capacity(100);
    /// assert!(mset.capacity() >= 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.elem_counts.capacity()
    }

    /// An iterator visitng all distinct elements and counts in arbitrary order.
    /// The iterator element type is `&'a (K, usize)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let mut mset = MultiSet::new();
    /// mset.insert("a");
    /// mset.insert("b");
    ///
    /// // Will print in an arbitrary order.
    /// for (elem, count) in mset.iter() {
    ///     println!("{}: {}", elem, count);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<K> {
        self.elem_counts.iter()
    }

    /// An iterator visiting all distinct elements in arbitrary order.
    /// The iterator element type is `&'a K`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('a');
    /// mset.insert('a');
    /// mset.insert('b');
    /// mset.insert('c');
    ///
    /// // Will print in an arbitrary order.
    /// for key in mset.keys() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<K, usize> {
        self.elem_counts.keys()
    }

    /// An iterator visiting all values in arbitrary order.
    /// The iterator element type is `&'a V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('a');
    /// mset.insert('a');
    /// mset.insert('b');
    /// mset.insert('c');
    ///
    /// // Will print in an arbitrary order.
    /// for val in mset.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values(&self) -> Values<K, usize> {
        self.elem_counts.values()
    }

    /// An iterator visiting all values mutably in arbitrary order.
    /// The iterator element type is `&'a mut V`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert_times('a', 1);
    /// mset.insert_times('b', 2);
    /// mset.insert_times('c', 3);
    ///
    /// for val in mset.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in mset.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<K, usize> {
        self.elem_counts.values_mut()
    }

    /// Returns the number of elements int he map.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// assert_eq!(mset.len(), 0);
    /// mset.insert_times('a', 10);
    /// assert_eq!(mset.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.elem_counts.len()
    }

    /// Returns `true` if the set contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// assert!(mset.is_empty());
    /// mset.insert('L');
    /// assert!(!mset.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elem_counts.is_empty()
    }

    /// Clears the set, returning all elements in an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<i32> = MultiSet::new();
    /// for u in &[1i32, 2i32, 3i32, 3i32, 2i32, 1i32] {
    ///     mset.insert(*u);
    /// }
    ///
    /// for (k, v) in mset.drain() {
    ///     assert!(k == 1 || k == 2 || k == 3);
    ///     assert_eq!(v, 2);
    /// }
    /// ```
    pub fn drain(&mut self) -> Drain<'_, K> {
        Drain {
            iter: self.elem_counts.drain(),
        }
    }

    /// Clears the multi set, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('v');
    /// assert_eq!(mset.is_empty(), false);
    /// mset.clear();
    /// assert!(mset.is_empty());
    /// ```
    pub fn clear(&mut self) {
        self.elem_counts.clear()
    }
}

impl<K: Hash + Eq, S: BuildHasher> MultiSet<K, S> {
    /// Create an empty `MultiSet` using the specified hasher.
    ///
    /// The created MutliSet has the default initial capacity.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut mset = MultiSet::with_hasher(s);
    /// mset.insert_times(1, 2);
    /// ```
    pub fn with_hasher(hash_builder: S) -> MultiSet<K, S> {
        MultiSet {
            elem_counts: HashMap::with_hasher(hash_builder),
        }
    }

    /// Create an empty `MultiSet` with the specified capacity, using `hash_builder`
    /// to hash the keys.
    ///
    /// The created MutliSet will hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the MultiSet will not allocate.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let s = RandomState::new();
    /// let mut mset = MultiSet::with_capacity_and_hasher(10, s);
    /// mset.insert_times(1, 2);
    /// ```
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> MultiSet<K, S> {
        MultiSet {
            elem_counts: HashMap::with_capacity_and_hasher(capacity, hash_builder),
        }
    }

    /// Returns a reference to the map's [`BuildHasher`].
    ///
    /// [`BuildHasher`]: trait.BuildHasher.html
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// use std::collections::hash_map::RandomState;
    ///
    /// let hasher = RandomState::new();
    /// let mset: MultiSet<i32> = MultiSet::with_hasher(hasher);
    /// let hasher: &RandomState = mset.hasher();
    /// ```
    pub fn hasher(&self) -> &S {
        self.elem_counts.hasher()
    }

    /// Reserves capacity for at least `additional` more elements to be inserted
    /// in the `HashMap`. The collection may reserve more space to avoid
    /// frequent reallocations.
    ///
    /// # Panics
    ///
    /// Panics if the new allocation size overflows [`usize`].
    ///
    /// [`usize`]: primitive.usize.html
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<&str> = MultiSet::new();
    /// mset.reserve(10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.elem_counts.reserve(additional)
    }

    /// Shrinks the capacity of the multi set as much as possible. It will
    /// drop down while maintaining the internal rules and possibly leaving
    /// some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<i8> = MultiSet::with_capacity(100);
    /// mset.insert(1i8);
    /// mset.insert(2i8);
    /// assert!(mset.capacity() >= 100);
    /// mset.shrink_to_fit();
    /// assert!(mset.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.elem_counts.shrink_to_fit();
    }

    /// Creat a `MultiSet` with the same BuildHasher type.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// use std::collections::HashMap;
    ///
    /// let mut m = HashMap::new();
    /// m.insert('a', 4);
    /// m.insert('z', 1);
    ///
    /// let mset: MultiSet<char> = MultiSet::from_hashmap(m);
    /// assert_eq!(mset.len(), 2);
    /// ```
    pub fn from_hashmap(rhs: HashMap<K, usize, S>) -> Self {
        Self { elem_counts: rhs }
    }

    /// Add a value to the multi set.
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    ///
    /// assert!(mset.insert('a'));
    /// assert!(!mset.insert('a'));
    /// assert_eq!(mset.len(), 1);
    /// ```
    pub fn insert(&mut self, value: K) -> bool {
        self.insert_times(value, 1)
    }

    /// Add a value to the multi set some number of times
    ///
    /// If the set did not have this value present, `true` is returned.
    ///
    /// If the set did have this value present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    ///
    /// assert!(mset.insert_times('a', 10));
    /// assert!(!mset.insert_times('a', 2));
    /// assert_eq!(mset.len(), 1);
    /// assert_eq!(mset.get(&'a'), Some(&12));
    /// ```
    pub fn insert_times(&mut self, value: K, n: usize) -> bool {
        match self.elem_counts.entry(value) {
            Entry::Vacant(view) => {
                view.insert(n);
                true
            }
            Entry::Occupied(mut view) => {
                *view.get_mut() += n;
                false
            }
        }
    }

    /// Remove a value from the multi set. Returns whether the value was
    /// present in the set.
    ///
    /// The value may be any borrowed form of the multi set's value type,
    /// but [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the value type.
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    ///
    /// mset.insert_times('a', 1);
    /// assert_eq!(mset.capacity(), 1);
    /// assert_eq!(mset.remove(&'a'), true);
    /// assert_eq!(mset.remove(&'a'), false);
    /// mset.shrink_to_fit();
    /// assert_eq!(mset.capacity(), 0);
    /// ```
    pub fn remove(&mut self, value: &K) -> bool
    where
        K: Hash + Eq + Clone,
    {
        self.remove_times(value, 1)
    }

    /// Remove multiple values from the multi set. Returns whether the values
    /// were present in the set.
    ///
    /// The values may be any borrowed form of the multi set's value type,
    /// but [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the value type.
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert_times('c', 10);
    /// assert_eq!(mset.remove_times(&'c', 2), true);
    /// assert_eq!(mset.remove_times(&'c', 10), false);
    /// assert_eq!(mset.len(), 0);
    ///
    /// assert!(mset.is_empty());
    /// ```
    pub fn remove_times(&mut self, value: &K, n: usize) -> bool
    where
        K: Hash + Eq + Clone,
    {
        match self.elem_counts.entry((*value).clone()) {
            Entry::Occupied(mut view) => {
                let curr_value = view.get().clone();
                if curr_value < n {
                    view.remove();
                    return false;
                } else {
                    let new_value = view.get() - n;
                    match new_value {
                        0 => view.remove(),
                        _ => view.insert(new_value),
                    };
                    return true;
                }
            }
            Entry::Vacant(__) => {
                return false;
            }
        };
    }

    /// Removes all instances of an element from the set and returns the
    /// multiplicity, if the element is in the set.
    ///
    /// The value may be any borrowd form of the set's value type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for
    /// the value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = vec!['a', 'b', 'c', 'b', 'a'].iter().cloned().collect();
    /// assert_eq!(mset.take(&'b'), Some(2));
    /// assert_eq!(mset.take(&'d'), None);
    /// ```
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    pub fn take(&mut self, value: &K) -> Option<usize> {
        self.elem_counts.remove_entry(value).map(|(_, v)| v)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(k, v)` such that `f(&k, &mut v)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = vec!['a', 'b', 'c', 'b', 'a'].iter().cloned().collect();
    /// mset.retain(|_, v: &usize| v % 2 == 0);
    /// assert_eq!(mset.len(), 2);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &usize) -> bool,
    {
        self.elem_counts.retain(|k, v| f(k, v));
    }

    /// Visits the values representing the difference,
    /// i.e., the values that are in `self` but no in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let p: MultiSet<_> = ['a', 'b', 'c', 'd'].iter().cloned().collect();
    /// let q: MultiSet<_> = ['d', 'b', 'c', 'd'].iter().cloned().collect();
    ///
    /// for e in p.difference(&q) {
    ///     println!("{}", e);
    /// }
    ///
    /// // can be thought of us `p - q`
    /// let diff: MultiSet<_> = p.difference(&q).collect();
    /// assert_eq!(diff, ['a'].iter().collect());
    ///
    /// // note that difference is not symetric,
    /// // and `q - p` has a different result:
    /// let diff: MultiSet<_> = q.difference(&p).collect();
    /// assert_eq!(diff, ['d'].iter().collect());
    /// ```
    pub fn difference<'a>(&'a self, other: &'a MultiSet<K, S>) -> Difference<'a, K, S> {
        Difference {
            iter: self.iter(),
            other,
        }
    }

    /// Returns `true` if the set contains a value.
    ///
    /// The value may be any borrowed form of the multiset's value type, but
    /// [`Hash`] and [`Eq`] on the borrowed form *must* match those for the
    /// value type.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<i32> = MultiSet::new();
    /// mset.insert_times(1, 10);
    /// mset.insert_times(2, 2);
    ///
    /// assert_eq!(mset.contains(&1), true);
    /// assert_eq!(mset.contains(&5), false);
    /// ```
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    pub fn contains<Q: ?Sized>(&self, value: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.contains_key(value)
    }

    /// Returns a reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the multi set's key type,
    /// but `Hash` and `Eq` on the borrowed form *must* match those
    /// for the key type.
    ///
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('a');
    /// assert_eq!(mset.get(&'a'), Some(&1));
    /// assert_eq!(mset.get(&'b'), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.get(key)
    }

    /// Returns a mutable reference to the value corresponding to the key.
    ///
    /// The key may be any borrowed form of the map's key type, but [`Hash`]
    /// and [`Eq`] on the borrowed form *must* match those for the key type.
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('a');
    ///
    /// if let Some(x) = mset.get_mut(&'a') {
    ///     *x = 5;
    /// }
    /// assert_eq!(mset.get(&'a'), Some(&5));
    ///
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut usize>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.get_mut(key)
    }

    /// Returns the key-value pair corresponding to the supplied key.
    ///
    /// The supplied key may be any borrowed form of the map's key type,
    /// but `Hash` and `Eq` on the borrowed form *must* match those for
    /// the key type.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('a');
    /// assert_eq!(mset.get_key_value(&'a'), Some((&'a', &1)));
    /// assert_eq!(mset.get_key_value(&'b'), None);
    /// ```
    pub fn get_key_value(&self, key: &K) -> Option<(&K, &usize)>
    where
        K: Borrow<K>,
    {
        self.elem_counts.get_key_value(key)
    }
}

pub struct Drain<'a, K: 'a> {
    iter: MapDrain<'a, K, usize>,
}

impl<'a, K> Iterator for Drain<'a, K> {
    type Item = (K, usize);

    fn next(&mut self) -> Option<(K, usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<K: Hash + Eq, S: BuildHasher + Default> Default for MultiSet<K, S> {
    /// Creates a new, empty `MultiSet`.
    fn default() -> Self {
        MultiSet {
            elem_counts: HashMap::default(),
        }
    }
}

impl<K: Eq + Hash, S: BuildHasher> PartialEq for MultiSet<K, S> {
    fn eq(&self, other: &MultiSet<K, S>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<K: Eq + Hash, S: BuildHasher> MultiSet<K, S> {}

impl<K: Eq + Hash + fmt::Debug, S: BuildHasher> fmt::Debug for MultiSet<K, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<K, S> FromIterator<K> for MultiSet<K, S>
where
    K: Hash + Eq,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> MultiSet<K, S> {
        let iter = iter.into_iter();
        let mut mset: MultiSet<K, S> = MultiSet::with_hasher(Default::default());
        for key in iter {
            mset.insert(key);
        }
        mset
    }
}

impl<K, S> FromIterator<(K, usize)> for MultiSet<K, S>
where
    K: Hash + Eq,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = (K, usize)>>(iter: I) -> MultiSet<K, S> {
        let mut mset = MultiSet::with_hasher(Default::default());
        mset.extend(iter);
        mset
    }
}

impl<K, S> IntoIterator for MultiSet<K, S>
where
    K: Hash + Eq + Clone,
    S: BuildHasher + Default,
{
    type Item = (K, usize);
    type IntoIter = IntoIter<K>;

    fn into_iter(self) -> <Self as IntoIterator>::IntoIter {
        self.elem_counts.into_iter()
    }
}

impl<'a, K, S> IntoIterator for &'a MultiSet<K, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    type Item = (&'a K, &'a usize);
    type IntoIter = Iter<'a, K>;

    fn into_iter(self) -> <Self as IntoIterator>::IntoIter {
        self.elem_counts.iter()
    }
}

impl<'a, K, S> IntoIterator for &'a mut MultiSet<K, S>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    type Item = (&'a K, &'a mut usize);
    type IntoIter = IterMut<'a, K>;

    fn into_iter(self) -> <Self as IntoIterator>::IntoIter {
        self.elem_counts.iter_mut()
    }
}

impl<K: Eq + Hash, S: BuildHasher> Extend<(K, usize)> for MultiSet<K, S> {
    fn extend<I: IntoIterator<Item = (K, usize)>>(&mut self, iter: I) {
        for (key, value) in iter.into_iter() {
            self.insert_times(key, value);
        }
    }
}

impl<'a, K, S> Extend<(&'a K, &'a usize)> for MultiSet<K, S>
where
    K: Eq + Hash + Copy,
    S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = (&'a K, &'a usize)>>(&mut self, iter: I) {
        for (key, value) in iter.into_iter().map(|(k, v)| ((*k).clone(), (*v).clone())) {
            self.insert_times(key, value);
        }
    }
}

impl<K, S> Extend<K> for MultiSet<K, S>
where
    K: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = K>>(&mut self, iter: I) {
        for key in iter.into_iter() {
            self.insert(key);
        }
    }
}

impl<'a, K, S> Extend<&'a K> for MultiSet<K, S>
where
    K: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = &'a K>>(&mut self, iter: I) {
        for key in iter.into_iter().map(|k| (*k).clone()) {
            self.insert(key.clone());
        }
    }
}

pub struct Difference<'a, K, S> {
    // iterator of the first set
    iter: Iter<'a, K>,
    // the second set
    other: &'a MultiSet<K, S>,
}

impl<K, S> Clone for Difference<'_, K, S> {
    fn clone(&self) -> Self {
        Difference {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, K: Eq + Hash, S: BuildHasher> Iterator for Difference<'a, K, S> {
    type Item = &'a K;

    fn next(&mut self) -> Option<&'a K> {
        loop {
            let (elem, count) = self.iter.next()?;
            let other_count = match self.other.get(elem) {
                Some(c) => c.clone(),
                None => 0usize,
            };

            if count > &other_count {
                let result = count - other_count;

                while result > 0 {
                    return Some(elem);
                }
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<K: Eq + Hash, S: BuildHasher> FusedIterator for Difference<'_, K, S> {}

impl<K: fmt::Debug + Eq + Hash, S: BuildHasher> fmt::Debug for Difference<'_, K, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    #[test]
    fn test_create_new_msets() {
        type MSC = MultiSet<char>;

        let mset = MSC::new();
        assert_eq!(mset.capacity(), 0);

        let mset = MSC::default();
        assert_eq!(mset.capacity(), 0);

        let mset = MSC::with_hasher(RandomState::new());
        assert_eq!(mset.capacity(), 0);

        let mset = MSC::with_capacity(0);
        assert_eq!(mset.capacity(), 0);

        let mset = MSC::with_capacity_and_hasher(0, RandomState::new());
        assert_eq!(mset.capacity(), 0);

        let mut mset = MSC::new();
        mset.insert_times('a', 2);
        mset.insert('b');
        mset.insert('b');
        mset.remove(&'a');
        mset.remove(&'a');
        mset.remove_times(&'b', 2);
        mset.shrink_to_fit();
        assert_eq!(mset.capacity(), 0);

        let mut m = MSC::new();
        m.reserve(0);
        assert_eq!(m.capacity(), 0);
    }

    #[test]
    fn test_insert_and_retrieve_elements() {
        let mut mset: MultiSet<char> = MultiSet::new();
        mset.insert('a');
        assert_eq!(mset.get(&'a'), Some(&1));
        mset.insert('a');
        assert_eq!(mset.get(&'a'), Some(&2));

        mset.insert_times('b', 5);
        assert_eq!(mset.get(&'b'), Some(&5));
    }

    #[test]
    fn test_iterator_over_elements() {
        let mut mset: MultiSet<char> = MultiSet::with_capacity(4);
        mset.insert_times('a', 10);
        mset.insert_times('b', 5);
        mset.insert_times('c', 1);

        let mut observed: usize = 0;
        let mut observed_len: usize = 0;

        for (_k, v) in &mset {
            observed_len += 1;
            observed += v;
        }

        assert_eq!(mset.len(), observed_len);
        assert_eq!(observed, 16);

        let mut mset = MultiSet::new();
        for i in 0..32 {
            assert!(mset.insert(i));
        }

        let mut observed: u32 = 0;
        let mut i = mset.iter();

        loop {
            match i.next() {
                Some((k, v)) => {
                    observed |= 1 << *k;
                    assert_eq!(*v, 1);
                }
                None => break,
            }
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_retrieving_mset_values() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert_times('d', 9);

        assert_eq!(m1.get(&'d'), Some(&9));
        assert_eq!(m1.get(&'u'), None);
    }

    #[test]
    fn test_mset_clear() {
        let mut mset: MultiSet<char> = MultiSet::new();

        assert!(mset.is_empty());

        mset.insert_times('c', 3);

        assert!(!mset.is_empty());

        assert_eq!(mset.get(&'c'), Some(&3));

        mset.clear();

        assert!(mset.is_empty());
    }

    #[test]
    fn test_difference() {
        let p: MultiSet<_> = [11, 3, 5, 11].iter().cloned().collect();
        let q: MultiSet<_> = [1, 3, 6, 11].iter().cloned().collect();

        let expected = [5, 11];
        for e in p.difference(&q) {
            assert!(expected.contains(e));
        }

        let expected = [1, 6];
        for e in q.difference(&p) {
            assert!(expected.contains(e));
        }
    }

    #[test]
    fn test_move_iter() {
        let mset = {
            let mut mset = MultiSet::new();

            mset.insert('a');
            mset.insert_times('b', 2);

            mset
        };

        let v = mset.into_iter().collect::<Vec<(char, usize)>>();
        assert!(v == [('a', 1), ('b', 2)] || v == [('b', 2), ('a', 1)]);
    }

    #[test]
    fn test_eq() {
        let mut mset = MultiSet::new();

        mset.insert(1);
        mset.insert(2);
        mset.insert(2);
        mset.insert(3);

        let mut other_mset = MultiSet::new();

        other_mset.insert(1);
        other_mset.insert(2);
        other_mset.insert(3);

        assert!(mset != other_mset);

        other_mset.insert(2);

        assert_eq!(mset, other_mset);
    }

    #[test]
    fn test_show_trivial() {
        assert_eq!(format!("{:?}", MultiSet::<i32>::new()), "{}");
    }

    #[test]
    fn test_show_nontrivial() {
        let mset: MultiSet<usize> = [777, 7, 7, 7].iter().cloned().collect();

        let debug_str = format!("{:?}", mset);
        assert!((debug_str == "{(777, 1), (7, 3)}") || (debug_str == "{(7, 3), (777, 1)}"));
    }

    #[test]
    fn test_drain_trivial() {
        let mut mset = MultiSet::<char>::new();
        for _ in mset.drain() {}
        assert!(mset.is_empty());

        let mut mset = MultiSet::<char>::new();
        drop(mset.drain());
        assert!(mset.is_empty());
    }

    #[test]
    fn test_drain_nontrivial() {
        let mut mset: MultiSet<_> = (1..100).collect();

        for _ in 0..20 {
            assert_eq!(mset.len(), 99);

            {
                let mut last_i = 0;
                let mut d = mset.drain();
                for (i, (e, c)) in d.by_ref().take(50).enumerate() {
                    last_i = i;
                    assert!(e != 0);
                    assert_eq!(c, 1);
                }

                assert_eq!(last_i, 49);
            }

            for _ in &mset {
                panic!("mset should be empty! this code should never be reached!");
            }

            mset.extend(1..100);
        }
    }

    #[test]
    fn test_extend_ref() {
        let mut a = MultiSet::new();
        a.insert(1);

        a.extend(&[1, 2, 3, 4]);

        assert_eq!(a.len(), 4);
        assert!(a.contains(&1));
        assert!(a.contains(&2));
        assert!(a.contains(&3));
        assert!(a.contains(&4));

        assert_eq!(a.get(&1), Some(&2));
        assert_eq!(a.get(&2), Some(&1));
        assert_eq!(a.get(&5), None);

        let mut b = MultiSet::new();
        b.insert(1);
        b.insert(2);
        b.insert(5);

        a.extend(&b);

        assert_eq!(a.len(), 5);
        assert!(a.contains(&1));
        assert!(a.contains(&2));
        assert!(a.contains(&3));
        assert!(a.contains(&4));
        assert!(a.contains(&5));
        assert_eq!(a.get(&1), Some(&3));
        assert_eq!(a.get(&2), Some(&2));
        assert_eq!(a.get(&5), Some(&1));
    }

    #[test]
    fn test_retain() {
        let mut mset: MultiSet<i32> = [1, 2, 3, 4, 5, 4, 3, 2, 1].iter().cloned().collect();
        mset.retain(|&k, v| k < 3);
        assert_eq!(mset.len(), 2);
        assert_eq!(mset.get(&1), Some(&2usize));
        assert_eq!(mset.get(&2), Some(&2usize));
    }
}
