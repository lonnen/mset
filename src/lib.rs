use std::borrow::Borrow;
use std::collections::hash_map::RandomState;
use std::collections::hash_map::{Drain as MapDrain, Entry, Keys, Values, ValuesMut};
use std::collections::HashMap;
use std::default::Default;
use std::hash::{BuildHasher, Hash};
use std::iter::FromIterator;

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
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MultiSet<K, S = RandomState>
where
    K: Hash + Eq,
    S: BuildHasher,
{
    elem_counts: HashMap<K, usize, S>,
}

impl<K: Hash + Eq, S: BuildHasher> MultiSet<K, S> {
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
    pub fn new() -> MultiSet<K, S>
    where
        S: Default,
    {
        Default::default()
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
    pub fn with_capacity(capacity: usize) -> MultiSet<K, S>
    where
        S: Default,
    {
        MultiSet {
            elem_counts: HashMap::with_capacity_and_hasher(capacity, Default::default()),
        }
    }

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

    // pub fn entry(&mut self, key: K) -> Entry<'_, K, usize> {
    //  // maybe this needs implementing?
    // }

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
        Drain { iter: self.elem_counts.drain() }
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
                let v = view.get_mut();
                *v += n;
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
    /// assert_eq!(mset.remove(&'a'), true);
    /// assert_eq!(mset.remove(&'a'), false);
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
                if view.get() < &n {
                    view.remove();
                    return false;
                } else {
                    let new_value = view.get() - n;
                    view.insert(new_value);
                    return true;
                }
            }
            Entry::Vacant(__) => {
                return false;
            }
        };
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

impl<K, S> FromIterator<K> for MultiSet<K, S>
where
    K: Hash + Eq + Clone,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = K>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut mset = Self::with_capacity(iter.size_hint().0);
        for key in iter {
            mset.insert(key);
        }
        mset
    }
}

impl<'a, K, S> FromIterator<&'a K> for MultiSet<K, S>
where
    K: Hash + Eq + Clone,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = &'a K>>(iter: I) -> Self {
        let iter = iter.into_iter();
        let mut mset = Self::with_capacity(iter.size_hint().0);
        for key in iter.map(|ref key| (*key).clone()) {
            mset.insert(key);
        }
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
    S: BuildHasher
{
    type Item = (&'a K, &'a mut usize);
    type  IntoIter = IterMut<'a, K>;

    fn into_iter(self) -> <Self as IntoIterator>::IntoIter {
        self.elem_counts.iter_mut()
    }
}

#[cfg(test)]
#[allow(unused_variables)]
mod tests {
    use super::*;

    #[test]
    fn test_create_new_msets() {
        let mset: MultiSet<char> = MultiSet::new();
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
    }

    // #[test]
    // fn test_union_of_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.insert('a');
    //     m1.insert('b');
    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     m2.insert_times('b', 10);

    //     let mut m3: MultiSet<char> = m1.union(m2);
    //     assert_eq!(m3.get(&'a'), Some(&1));
    //     assert_eq!(m3.get(&'b'), Some(&11));
    // }

    // // #[test]
    // // fn copy_msets(){ }

    // #[test]
    // fn test_mset_difference() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.insert('a', 3);
    //     m1.insert('c', 5);

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     m2.insert('a', 1);
    //     ms.insert('b', 1);

    //     let m1d2: MultiSet<char> = m1.difference(m2);
    //     assert_eq!(m1d2.get('a'), Some(2));
    //     assert_eq!(m1d2.get('c'), Some(5));

    //     let m2d1: MultiSet<char> = m2.difference(m1);
    //     assert_eq!(m2d1.get('b'), Some(1));
    // }

    // #[test]
    // fn test_difference_update() {
    //     return true; // TODO mod in place
    // }

    #[test]
    fn test_retrieving_mset_values() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert_times('d', 9);

        assert_eq!(m1.get(&'d'), Some(&9));
        assert_eq!(m1.get(&'u'), None);
    }

    // #[test]
    // fn test_intersection_of_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.insert('a', 2);

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     m2.insert('a', 1);
    //     m2.insert('b', 3);

    //     let m3: MultiSet<char> = m1.intersection(m2);
    //     let m4: MultiSet<char> = m2.intersection(m1);
    //     assert_eq!(m3, m4);
    //     assert_eq!(m3.get('a'), Some(1));
    // }

    // #[test]
    // fn test_msets_within_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.insert('a', 2);

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     m2.insert('a', 1);
    //     m2.insert('b', 3);

    //     let mut m3: MultiSet<char> = MultiSet::new();
    //     m3.insert('a', 1);

    //     let mut m4: MultiSet<char> = MultiSet::new();
    //     m4.insert('x', 777);

    //     // some overlapping elements
    //     assert!(!m1.is_disjoint(m2));
    //     assert!(!m1.is_disjoint(m3));

    //     assert!(!m1.is_subset(m2));
    //     assert!(!m1.is_subset(m3));

    //     assert!(!m1.is_superset(m2));
    //     assert!(!m1.is_superset(m3));

    //     // no overlap at all
    //     assert!(m1.is_disjoint(m4));

    //     // is_disjoint is symmetric
    //     assert!(!m2.is_disjoint(m1));
    //     assert!(!m3.is_disjoint(m1));
    //     assert!(m4.is_disjoint(m1));

    //     // one contained within another
    //     assert!(m3.is_subset(m1));
    //     assert!(m3.is_subset(m2));

    //     assert!(m1.is_superset(m3));
    //     assert!(m2.is_superset(m3));

    //     // is_subset and is_superset are symmetric to one another
    //     assert!(m1.is_superset(m3));
    //     assert!(m2.is_superset(m3));

    //     assert!(m3.is_subset(m1));
    //     assert!(m3.is_subset(m1));
    // }

    // #[test]
    // fn test_ways_to_retrieve_the_contents_of_an_mset() {
    //     let mut mset: MultiSet<char> = MultiSet::new();

    //     let v1: Vec<char> = vec!['a', 'b', 'b', 'c', 'c', 'c'];

    //     for c in v1 {
    //         mset.insert(c);
    //     }

    //     let keys = mset.distinct_elements();
    //     assert_eq!(keys.len(), 3);
    //     assert!(keys.contains('a'));
    //     assert!(keys.contains('b'));
    //     assert!(keys.contains('c'));

    //     let counts = mset.multiplicites();
    //     assert_eq!(counts.len(), 3);

    //     let mut observed: usize = 0;
    //     for i in items {
    //         observed += i;
    //     }
    //     assert_eq!(observed, 6);

    //     let items = mset.items();
    //     let v2: Vec<char> = Vec::new();
    //     assert_eq!(items.len(), 3);
    //     for (k, v) in items {
    //         for _ in 0..v {
    //             v2.push(k);
    //         }
    //     }
    //     assert_eq!(v2.sort(), v1);
    // }

    // #[test]
    // fn test_symmetric_difference() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     let v1: Vec<char> = vec!['a', 'a', 'b'];

    //     for c in v1 {
    //         mset.insert(c);
    //     }

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     let v2: Vec<char> = vec!['a', 'a', 'a', 'c'];

    //     for c in v3 {
    //         mset.insert(c);
    //     }

    //     let sd1 = m1.test_symmetric_difference(m2);
    //     let sd2 = m2.test_symmetric_difference(m1);

    //     assert_eq!(sd1, sd2);
    //     assert_eq!(sd1.len(), 3);
    //     assert_eq!(sd1.distinct_elements().sort(), vec!['a', 'b', 'c']);
    // }

    // #[test]
    // fn test_scalar_multiplication() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     let v1: Vec<char> = vec!['a', 'a', 'b'];

    //     for c in v1 {
    //         m1.insert(c);
    //         m2.insert(c);
    //         m2.insert(c);
    //     }

    //     assert_eq!(m1.times(2), m2);
    // }

    // #[tests]
    // fn test_union_of_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     let mut m2: MultiSet<char> = MultiSet::new();

    //     for c in vec!['a', 'a', 'b'] {
    //         m1.insert(c);
    //     }

    //     for c in vec!['a', 'a', 'b'] {
    //         m2.insert(c);
    //     }

    //     let mut m3: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'a', 'b'] {
    //         m3.insert(c);
    //     }

    //     assert_eq!(m1.union(m2), m3);
    // }

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

    // #[tests]
    // fn test_difference_update() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b', 'b', 'b', 'c'] {
    //         m1.insert(c);
    //     }

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'b', 'd'] {
    //         m2.insert(c);
    //     }

    //     let mut m3: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'b', 'b', 'c'] {
    //         m3.insert(c);
    //     }

    //     assert_eq!(m1.difference_update(m2), m3);
    // }

    // #[tests]
    // fn test_discard() {
    //     let mut mset: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b', 'b', 'b', 'c'] {
    //         mset.insert(c);
    //     }

    //     mset.discard('b');

    //     let mut expected: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'c'] {
    //         mset.insert(c);
    //     }

    //     assert_eq!(mset, expected);
    // }

    // #[tests]
    // fn test_intersection_update() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b'] {
    //         m1.insert(c);
    //     }

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     for c in vec!['b', 'c'] {
    //         m2.insert(c);
    //     }

    //     let mut expected: MultiSet<char> = MultiSet::new();
    //     for c in vec!['b'] {
    //         mset.insert(c);
    //     }

    //     m1.intersection_update(m2);
    //     assert_eq!(m1, expected);
    // }

    // #[tests]
    // fn test_pop() {
    //     let mut mset: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b'] {
    //         mset.insert(c);
    //     }

    //     let expected = mset.pop('z');

    //     assert_eq!(mset.pop('a'), Some(2));
    //     assert_eq!(mset.pop('z'), None);
    // }

    // #[tests]
    // fn test_remove() {

    // }

    // #[tests]
    // fn test_symmetric_difference_update() {}

    // #[tests]
    // fn test_times_update() {}

    // #[tests]
    // fn test_union_update() {}

    // #[tests]
    // fn test_update() {}
}
