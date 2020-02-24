use std::borrow::Borrow;
use std::cmp::min;
use std::collections::hash_map::RandomState;
use std::collections::hash_map::{Drain as MapDrain, Entry, Iter as MapIter, Keys};
use std::collections::HashMap;
use std::default::Default;
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::{Chain, FromIterator, FusedIterator};
use std::ops::{BitAnd, BitOr, BitXor, Sub};

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
/// item's hash, as determined by the [`Hash`] trait, or its equality, as
/// determined by the [`Eq`] trait, changes while it is in the set. This is
/// normally only possible through [`Cell`], [`RefCell`], global state, I/O, or
/// unsafe code.
///
/// # Examples
///
/// ```
/// use mset::MultiSet;
///
/// // Ocassionally, type inference will let us omit an explicit type signature
/// // (which would be `MultiSet<String>` in this example).
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
/// bag.remove(&"23".to_string());
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
/// ```
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
/// ```
/// use mset::MultiSet;
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
pub struct MultiSet<T, S = RandomState> {
    elem_counts: HashMap<T, usize, S>,
}

impl<T: Hash + Eq> MultiSet<T, RandomState> {
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
    pub fn new() -> MultiSet<T, RandomState> {
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
    pub fn with_capacity(capacity: usize) -> MultiSet<T, RandomState> {
        MultiSet {
            elem_counts: HashMap::with_capacity(capacity),
        }
    }
}

impl<T, S> MultiSet<T, S> {
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
    /// The iterator element type is `&'a (T, usize)`.
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
    pub fn iter(&self) -> Iter<T> {
        Iter {
            iter: self.elem_counts.iter(),
        }
    }

    /// An iterator visitng all distinct elements and counts in arbitrary order.
    /// The iterator element type is `&'a (T, usize)`.
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
    /// for (elem, count) in mset.element_counts() {
    ///     println!("{}: {}", elem, count);
    /// }
    /// ```
    pub fn element_counts(&self) -> MapIter<T, usize> {
        self.elem_counts.iter()
    }

    /// An iterator visiting all distinct elements in arbitrary order.
    /// The iterator element type is `&'a T`.
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
    /// for e in mset.elements() {
    ///     println!("{}", e);
    /// }
    /// ```
    pub fn elements(&self) -> Keys<T, usize> {
        self.elem_counts.keys()
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
    /// for (e, m) in mset.drain() {
    ///     assert!(e == 1 || e == 2 || e == 3);
    ///     assert_eq!(m, 2);
    /// }
    /// ```
    pub fn drain(&mut self) -> Drain<'_, T> {
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

impl<T: Hash + Eq, S: BuildHasher> MultiSet<T, S> {
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
    pub fn with_hasher(hash_builder: S) -> MultiSet<T, S> {
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
    pub fn with_capacity_and_hasher(capacity: usize, hash_builder: S) -> MultiSet<T, S> {
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
    pub fn from_hashmap(rhs: HashMap<T, usize, S>) -> Self {
        Self { elem_counts: rhs }
    }

    /// Returns `true` if `self` has no elements in common with `other`.
    /// This is equivalent to checking for an empty intersection.
    ///
    /// # Examples
    /// ```
    /// use mset::MultiSet;
    ///
    /// let p: MultiSet<_> = [1, 2, 2, 3].iter().cloned().collect();
    /// let mut q = MultiSet::new();
    ///
    /// assert!(p.is_disjoint(&q));
    /// q.insert(0);
    /// assert!(p.is_disjoint(&q));
    /// q.insert(4);
    /// assert!(p.is_disjoint(&q));
    /// q.insert(3);
    /// assert_eq!(p.is_disjoint(&q), false);
    /// ```
    pub fn is_disjoint(&self, other: &MultiSet<T, S>) -> bool {
        self.iter().all(|(e, _)| !other.contains(e))
    }

    /// Returns `true` if the multiset is a subset of another,
    /// i.e., `other` contains at least all the values in `self`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let msup: MultiSet<_> = [1, 2, 2, 3].iter().cloned().collect();
    /// let mut mset = MultiSet::new();
    ///
    /// assert!(mset.is_subset(&msup));
    /// mset.insert(2);
    /// assert!(mset.is_subset(&msup));
    /// mset.insert(2);
    /// assert!(mset.is_subset(&msup));
    /// mset.insert(2);
    /// assert_eq!(mset.is_subset(&msup), false);
    /// ```
    pub fn is_subset(&self, other: &MultiSet<T, S>) -> bool {
        self.iter().all(|(e, m)| match other.get(e) {
            Some(o_m) => m <= o_m,
            None => false,
        })
    }

    /// Returns `true` if the multiset is a superset of another,
    /// i.e., `self` contains at least all the values in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let msub: MultiSet<_> = [1, 2, 2].iter().cloned().collect();
    /// let mut mset = MultiSet::new();
    ///
    /// assert_eq!(mset.is_superset(&msub), false);
    ///
    /// mset.insert(0);
    /// mset.insert(1);
    /// assert_eq!(mset.is_superset(&msub), false);
    ///
    /// mset.insert(2);
    /// assert_eq!(mset.is_superset(&msub), false);
    ///
    /// mset.insert(2);
    /// assert_eq!(mset.is_superset(&msub), true);
    /// ```
    pub fn is_superset(&self, other: &MultiSet<T, S>) -> bool {
        other.is_subset(self)
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
    pub fn insert(&mut self, value: T) -> bool {
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
    pub fn insert_times(&mut self, value: T, n: usize) -> bool {
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
    pub fn remove(&mut self, value: &T) -> bool
    where
        T: Hash + Eq + Clone,
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
    pub fn remove_times(&mut self, value: &T, n: usize) -> bool
    where
        T: Hash + Eq + Clone,
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
    pub fn take(&mut self, value: &T) -> Option<usize> {
        self.elem_counts.remove_entry(value).map(|(_, v)| v)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(elem, multiplicty)` such that `f(&k, &mut v)`
    /// returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = vec!['a', 'b', 'c', 'b', 'a'].iter().cloned().collect();
    /// mset.retain(|_, m: &usize| m % 2 == 0);
    /// assert_eq!(mset.len(), 2);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T, &usize) -> bool,
    {
        self.elem_counts.retain(|e, m| f(e, m));
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
    /// // can be thought of as `p - q`
    /// let diff: MultiSet<_> = p.difference(&q).collect();
    /// assert_eq!(diff, ['a'].iter().collect());
    ///
    /// // note that difference is not symetric,
    /// // and `q - p` has a different result:
    /// let diff: MultiSet<_> = q.difference(&p).collect();
    /// assert_eq!(diff, ['d'].iter().collect());
    /// ```
    pub fn difference<'a>(&'a self, other: &'a MultiSet<T, S>) -> Difference<'a, T, S> {
        Difference {
            iter: self.iter(),
            other,
        }
    }

    /// Visits the values representing the symmetric difference,
    /// i.e., the values that are in `self` or in `other` but not in both.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let p: MultiSet<_> = ['a', 'b', 'c', 'd'].iter().cloned().collect();
    /// let q: MultiSet<_> = ['d', 'b', 'c', 'd'].iter().cloned().collect();
    ///
    /// for e in p.symmetric_difference(&q) {
    ///     println!("{}", e);
    /// }
    ///
    /// let diff1: MultiSet<_> = p.symmetric_difference(&q).collect();
    /// let diff2: MultiSet<_> = q.symmetric_difference(&p).collect();
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, ['a', 'd'].iter().collect());
    /// ```
    pub fn symmetric_difference<'a>(
        &'a self,
        other: &'a MultiSet<T, S>,
    ) -> SymmetricDifference<'a, T, S> {
        SymmetricDifference {
            iter: self.difference(other).chain(other.difference(self)),
        }
    }

    /// Visits the values representing the intersection,
    /// i.e., the values that are both in `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let p: MultiSet<_> = ['a', 'b', 'c', 'd'].iter().cloned().collect();
    /// let q: MultiSet<_> = ['d', 'b', 'c', 'd'].iter().cloned().collect();
    ///
    /// for e in p.intersection(&q) {
    ///     println!("{}", e);
    /// }
    ///
    /// let diff1: MultiSet<_> = p.symmetric_difference(&q).collect();
    /// let diff2: MultiSet<_> = q.symmetric_difference(&p).collect();
    /// assert_eq!(diff1, diff2);
    /// assert_eq!(diff1, ['a', 'd'].iter().collect());
    /// ```
    pub fn intersection<'a>(&'a self, other: &'a MultiSet<T, S>) -> Intersection<'a, T, S> {
        Intersection {
            iter: self.iter(),
            other: other,
        }
    }

    /// Visits the values representing the union, i.e., all the values in `self` or `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let p: MultiSet<_> = ['a', 'b', 'c', 'd'].iter().cloned().collect();
    /// let q: MultiSet<_> = ['b', 'c', 'd'].iter().cloned().collect();
    ///
    /// // Print 'a', 'b', 'b', 'c', 'c', 'd', 'd', 'd' in an arbitrary order.
    /// for e in p.union(&q) {
    ///     println!("{}", e);
    /// }
    ///
    /// let union: MultiSet<_> = p.union(&q).collect();
    /// assert_eq!(union, ['a', 'b', 'b', 'c', 'c', 'd', 'd'].iter().collect());
    /// ```
    pub fn union<'a>(&'a self, other: &'a MultiSet<T, S>) -> Union<'a, T> {
        Union {
            iter: self.iter().chain(other.iter()),
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
        T: Borrow<Q>,
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
        T: Borrow<Q>,
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
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.get_mut(key)
    }

    /// Returns the element-multiplicity pair corresponding to the supplied key.
    ///
    /// The supplied element may be any borrowed form of the mset's type,
    /// but `Hash` and `Eq` on the borrowed form *must* match those for
    /// the element type.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<char> = MultiSet::new();
    /// mset.insert('a');
    /// assert_eq!(mset.get_element_multiplicity(&'a'), Some((&'a', &1)));
    /// assert_eq!(mset.get_element_multiplicity(&'b'), None);
    /// ```
    pub fn get_element_multiplicity(&self, key: &T) -> Option<(&T, &usize)>
    where
        T: Borrow<T>,
    {
        self.elem_counts.get_key_value(key)
    }
}

impl<T: Hash + Eq, S: BuildHasher + Default> Default for MultiSet<T, S> {
    /// Creates a new, empty `MultiSet`.
    fn default() -> Self {
        MultiSet {
            elem_counts: HashMap::default(),
        }
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> BitOr<&MultiSet<T, S>> for &MultiSet<T, S> {
    type Output = MultiSet<T, S>;

    /// Returns the union of `self` and `rhs` (right hand side) as a new `MultiSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let p: MultiSet<_> = vec![1, 2, 3, 3].into_iter().collect();
    /// let q: MultiSet<_> = vec![3, 3, 4, 5].into_iter().collect();
    ///
    /// let mset = &p | &q;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 3, 3, 4, 5];
    /// for (e, m) in &mset {
    ///     assert!(expected.contains(e));
    ///     i += (e * m);
    /// }
    ///
    /// assert_eq!(i, expected.iter().sum());
    /// ```
    fn bitor(self, rhs: &MultiSet<T, S>) -> MultiSet<T, S> {
        self.union(rhs).cloned().collect()
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> BitAnd<&MultiSet<T, S>> for &MultiSet<T, S> {
    type Output = MultiSet<T, S>;

    /// Returns the intersection of `self` and `rhs` (right hand side) as a new `MultiSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let p: MultiSet<_> = vec![1, 2, 3, 3, 3].into_iter().collect();
    /// let q: MultiSet<_> = vec![2, 3, 4, 5].into_iter().collect();
    ///
    /// let mset = &p & &q;
    ///
    /// let mut i = 0;
    /// let expected = [2, 3];
    /// for (e, m) in &mset {
    ///     assert!(expected.contains(e));
    ///     println!("{} {}", e, m);
    ///     i += (e * m);
    /// }
    ///
    /// assert_eq!(i, expected.iter().sum());
    /// ```
    fn bitand(self, rhs: &MultiSet<T, S>) -> MultiSet<T, S> {
        self.intersection(rhs).cloned().collect()
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> BitXor<&MultiSet<T, S>> for &MultiSet<T, S> {
    type Output = MultiSet<T, S>;

    /// Returns the symmetric difference of `self` and `rhs` (right hand side) as a
    /// new `MultiSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let p: MultiSet<_> = vec![1, 2, 3, 3].into_iter().collect();
    /// let q: MultiSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let mset = &p ^ &q;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 3, 4, 5];
    /// for (e, m) in &mset {
    ///     assert!(expected.contains(e));
    ///     i += (e * m);
    /// }
    ///
    /// assert_eq!(i, expected.iter().sum());
    /// ```
    fn bitxor(self, rhs: &MultiSet<T, S>) -> MultiSet<T, S> {
        self.symmetric_difference(rhs).cloned().collect()
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> Sub<&MultiSet<T, S>> for &MultiSet<T, S> {
    type Output = MultiSet<T, S>;

    /// Returns the difference of `self` and `rhs` (right hand side) as a new `MultiSet<T, S>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let p: MultiSet<_> = vec![1, 2, 3, 3].into_iter().collect();
    /// let q: MultiSet<_> = vec![3, 4, 5].into_iter().collect();
    ///
    /// let mset = &p - &q;
    ///
    /// let mut i = 0;
    /// let expected = [1, 2, 3];
    /// for (e, m) in &mset {
    ///     assert!(expected.contains(e));
    ///     i += (e * m);
    /// }
    ///
    /// assert_eq!(i, expected.iter().sum());
    /// ```
    fn sub(self, rhs: &MultiSet<T, S>) -> MultiSet<T, S> {
        self.difference(rhs).cloned().collect()
    }
}

impl<T: Eq + Hash, S: BuildHasher> PartialEq for MultiSet<T, S> {
    fn eq(&self, other: &MultiSet<T, S>) -> bool {
        if self.len() != other.len() {
            return false;
        }

        self.iter()
            .all(|(key, value)| other.get(key).map_or(false, |v| *value == *v))
    }
}

impl<T: Eq + Hash, S: BuildHasher> Eq for MultiSet<T, S> {}

impl<T: Eq + Hash + fmt::Debug, S: BuildHasher> fmt::Debug for MultiSet<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.iter()).finish()
    }
}

impl<T, S> FromIterator<T> for MultiSet<T, S>
where
    T: Hash + Eq,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> MultiSet<T, S> {
        let iter = iter.into_iter();
        let mut mset: MultiSet<T, S> = MultiSet::with_hasher(Default::default());
        for key in iter {
            mset.insert(key);
        }
        mset
    }
}

impl<T, S> FromIterator<(T, usize)> for MultiSet<T, S>
where
    T: Hash + Eq,
    S: BuildHasher + Default,
{
    fn from_iter<I: IntoIterator<Item = (T, usize)>>(iter: I) -> MultiSet<T, S> {
        let mut mset = MultiSet::with_hasher(Default::default());
        mset.extend(iter);
        mset
    }
}

impl<T, S> IntoIterator for MultiSet<T, S>
where
    T: Hash + Eq + Clone,
    S: BuildHasher + Default,
{
    type Item = (T, usize);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            iter: self.elem_counts.into_iter(),
        }
    }
}

impl<'a, T, S> IntoIterator for &'a MultiSet<T, S>
where
    T: Hash + Eq,
    S: BuildHasher,
{
    type Item = (&'a T, &'a usize);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> <Self as IntoIterator>::IntoIter {
        self.iter()
    }
}

impl<T: Eq + Hash, S: BuildHasher> Extend<(T, usize)> for MultiSet<T, S> {
    fn extend<I: IntoIterator<Item = (T, usize)>>(&mut self, iter: I) {
        for (key, value) in iter.into_iter() {
            self.insert_times(key, value);
        }
    }
}

impl<'a, T, S> Extend<(&'a T, &'a usize)> for MultiSet<T, S>
where
    T: Eq + Hash + Copy,
    S: BuildHasher,
{
    fn extend<I: IntoIterator<Item = (&'a T, &'a usize)>>(&mut self, iter: I) {
        for (key, value) in iter.into_iter().map(|(k, v)| ((*k).clone(), (*v).clone())) {
            self.insert_times(key, value);
        }
    }
}

impl<T, S> Extend<T> for MultiSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for key in iter.into_iter() {
            self.insert(key);
        }
    }
}

impl<'a, T, S> Extend<&'a T> for MultiSet<T, S>
where
    T: Eq + Hash + Clone,
    S: BuildHasher + Default,
{
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for key in iter.into_iter().map(|k| (*k).clone()) {
            self.insert(key.clone());
        }
    }
}

/// An iterator over the items of a `MultiSet`.
///
/// This `struct` is created by the [`iter`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`iter`]: struct.MultiSet.html#method.iter
pub struct Iter<'a, T: 'a> {
    iter: ::std::collections::hash_map::Iter<'a, T, usize>,
}

impl<T> Clone for Iter<'_, T> {
    fn clone(&self) -> Self {
        Iter {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (&'a T, &'a usize);

    fn next(&mut self) -> Option<(&'a T, &'a usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for Iter<'_, T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for Iter<'_, T> {}

impl<T: fmt::Debug> fmt::Debug for Iter<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// An owning iterator over the items of a `MultiSet`.
///
/// This `struct` is created by the [`into_iter`] method on [`MultiSet`] (provided by the
/// `IntoIterator` trait). See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`into_iter`]: struct.MultiSet.html#method.into_iter
pub struct IntoIter<T> {
    iter: ::std::collections::hash_map::IntoIter<T, usize>,
}

impl<T> Iterator for IntoIter<T> {
    type Item = (T, usize);

    fn next(&mut self) -> Option<(T, usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for IntoIter<T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for IntoIter<T> {}

pub struct Drain<'a, T: 'a> {
    iter: MapDrain<'a, T, usize>,
}

impl<'a, T> Iterator for Drain<'a, T> {
    type Item = (T, usize);

    fn next(&mut self) -> Option<(T, usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A lazy iterator producing elements in the intersection of `MultiSet`s.
///
/// This `struct` is created by the [`intersection`] method on [`MultiSet`].
/// See its documentation for more.
///
/// ['MultiSet`]: struct.MultiSet.html
/// [intersection`]: struct.MultiSet.html#method.intersection
pub struct Intersection<'a, T: 'a, S: 'a> {
    // iterator of the first set
    iter: Iter<'a, T>,
    // the second set
    other: &'a MultiSet<T, S>,
}

impl<T, S> Clone for Intersection<'_, T, S> {
    fn clone(&self) -> Self {
        Intersection {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for Intersection<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let (elem, count) = self.iter.next()?;
            let other_count = match self.other.get(elem) {
                Some(c) => c.clone(),
                None => 0usize,
            };

            for _ in 0..min(*count, other_count) {
                return Some(elem);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let (_, upper) = self.iter.size_hint();
        (0, upper)
    }
}

impl<T: Eq + Hash, S: BuildHasher> FusedIterator for Intersection<'_, T, S> {}

/// A lazy iterator producing elements in the difference of `MultiSet`s.
///
/// This `struct` is created by the [`difference`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`difference`]: struct.MultiSet.html#method.difference
pub struct Difference<'a, T, S> {
    // iterator of the first set
    iter: Iter<'a, T>,
    // the second set
    other: &'a MultiSet<T, S>,
}

impl<T, S> Clone for Difference<'_, T, S> {
    fn clone(&self) -> Self {
        Difference {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for Difference<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
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

impl<T: Eq + Hash, S: BuildHasher> FusedIterator for Difference<'_, T, S> {}

impl<T: fmt::Debug + Eq + Hash, S: BuildHasher> fmt::Debug for Difference<'_, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the symmetric difference of `MultiSet`s.
///
/// This `struct` is created by the [`symmetric_difference`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`symmetric_difference`]: struct.MultiSet.html#method.symmetric_difference
pub struct SymmetricDifference<'a, T: 'a, S: 'a> {
    iter: Chain<Difference<'a, T, S>, Difference<'a, T, S>>,
}

impl<T, S> Clone for SymmetricDifference<'_, T, S> {
    fn clone(&self) -> Self {
        SymmetricDifference {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T: Eq + Hash, S: BuildHasher> Iterator for SymmetricDifference<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// A lazy iterator producing elements in the union of `MultiSet`s.
///
/// This `struct` is created by the [`union`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`union`]: struct.MultiSet.html#method.union
pub struct Union<'a, T: 'a> {
    iter: Chain<Iter<'a, T>, Iter<'a, T>>,
}

impl<T> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union {
            iter: self.iter.clone(),
        }
    }
}

impl<T: fmt::Debug + Eq + Hash> fmt::Debug for Union<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

impl<T: Eq + Hash> FusedIterator for Union<'_, T> {}

impl<'a, T: Eq + Hash> Iterator for Union<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            let (elem, count) = self.iter.next()?;
            let result = count.clone();
            while result > 0 {
                return Some(elem);
            }
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

#[cfg(test)]
mod test_mset {
    use super::MultiSet;
    use super::RandomState;

    #[test]
    fn test_zero_capacity() {
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

        for (_e, m) in &mset {
            observed_len += 1;
            observed += m;
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
                Some((e, m)) => {
                    observed |= 1 << *e;
                    assert_eq!(*m, 1);
                }
                None => break,
            }
        }
        assert_eq!(observed, 0xFFFF_FFFF);
    }

    #[test]
    fn test_iterator_over_element_counts() {
        let mut mset = MultiSet::new();
        for i in 0..32 {
            assert!(mset.insert(i));
        }

        let mut observed: u32 = 0;
        let mut i = mset.element_counts();

        loop {
            match i.next() {
                Some((e, m)) => {
                    observed |= 1 << *e;
                    assert_eq!(*m, 1);
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
    fn test_disjoint() {
        let mut p = MultiSet::new();
        let mut q = MultiSet::new();

        assert!(p.is_disjoint(&q));
        assert!(p.is_disjoint(&q));

        p.insert(5);
        q.insert(6);

        assert!(p.is_disjoint(&q));
        assert!(p.is_disjoint(&q));

        p.insert(7);
        p.insert(9);
        q.insert(4);
        q.insert(2);

        assert!(p.is_disjoint(&q));
        assert!(p.is_disjoint(&q));

        p.insert(2);

        assert_eq!(p.is_disjoint(&q), false);
        assert_eq!(p.is_disjoint(&q), false);
    }

    #[test]
    fn test_subset_and_superset() {
        let mut p: MultiSet<_> = [0, 5, 11, 7].iter().cloned().collect();
        let mut q: MultiSet<_> = [0, 7, 19, 250, 11, 200].iter().cloned().collect();

        assert_eq!(p.is_subset(&q), false);
        assert_eq!(p.is_superset(&q), false);
        assert_eq!(q.is_subset(&p), false);
        assert_eq!(q.is_superset(&p), false);

        p.insert(5);
        q.insert_times(5, 2);

        assert_eq!(p.is_subset(&q), true);
        assert_eq!(p.is_superset(&q), false);
        assert_eq!(q.is_subset(&p), false);
        assert_eq!(q.is_superset(&p), true);
    }

    #[test]
    fn test_union() {
        let p: MultiSet<_> = [11, 3, 5, 11].iter().cloned().collect();
        let q: MultiSet<_> = [1, 3, 6, 11].iter().cloned().collect();

        let mut i = 0;
        let expected = [1, 3, 3, 5, 6, 11, 11];
        for e in p.union(&q) {
            assert!(expected.contains(e));
            i += e;
        }

        assert_eq!(i, expected.iter().sum());
    }

    #[test]
    fn test_intersection() {
        let mut p = MultiSet::new();
        let mut q = MultiSet::new();

        assert!(p.intersection(&q).next().is_none());

        p.insert(11);
        p.insert(11);
        p.insert(1);
        p.insert(3);

        q.insert(3);
        q.insert(11);
        q.insert(11);
        q.insert(11);
        q.insert(77);

        let mut i = 0;
        let expected = [3, 11];
        for x in p.intersection(&q) {
            assert!(expected.contains(x));
            i += x;
        }
        assert_eq!(i, expected.iter().sum());
    }

    #[test]
    fn test_difference() {
        let p: MultiSet<_> = [3, 5, 5, 11, 11].iter().cloned().collect();
        let q: MultiSet<_> = [1, 3, 6, 11].iter().cloned().collect();

        let mut i = 0;
        let expected = [5, 11];
        for e in p.difference(&q) {
            assert!(expected.contains(e));
            i += e;
        }

        assert_eq!(i, expected.iter().sum());

        i = 0;
        let expected = [1, 6];
        for e in q.difference(&p) {
            assert!(expected.contains(e));
            i += e;
        }

        assert_eq!(i, expected.iter().sum());
    }

    #[test]
    fn test_symmetric_difference() {
        let p: MultiSet<_> = [1, 3, 3, 3, 3, 5, 9, 11].iter().collect();
        let q: MultiSet<_> = [2, 3, 3, 5, 9, 14, 22].iter().collect();

        let mut i = 0;
        let expected = [1, 3, 11, 2, 14, 22];
        for e in p.symmetric_difference(&q) {
            assert!(expected.contains(e));
            i += *e;
        }
        assert_eq!(i, expected.iter().sum());
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
        mset.insert('a');
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
        mset.retain(|&k, _v| k < 3);
        assert_eq!(mset.len(), 2);
        assert_eq!(mset.get(&1), Some(&2usize));
        assert_eq!(mset.get(&2), Some(&2usize));
    }
}
