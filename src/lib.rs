#![doc(html_root_url = "https://docs.rs/mset/0.1.1")]
//! A hash multiset implemented as a `HashMap` where the value is `usize`.
//!
//! A mset, multiset, or bag is a set that allows multiple occurances of an
//! element. This implementation is backed by an underlying [`HashMap`] instance
//! and supports an API similar to set with some additions to make multiple
//! additions and removals easier and a [`Clone`]constraint for efficiency of
//! storage.
//!
//! See the [`MultiSet`] struct documentation for more examples and specific
//! constraints.
//!
//! [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
//! [`HashMap`]: struct.HashMap.html
//! [`MultiSet`]: struct.MultiSet.html

use std::borrow::Borrow;
use std::cmp::min;
use std::collections::HashMap;
use std::collections::hash_map::{self, Entry, RandomState};
use std::fmt;
use std::hash::{BuildHasher, Hash};
use std::iter::{Chain, FromIterator, FusedIterator};
use std::ops;

/// A hash multiset implemented as a `HashMap` where the value is `usize`.
///
/// As with the [`HashMap`] type, a `MultiSet` requires that the elements
/// implement the [`Eq`] and [`Hash`] traits. This can frequently be achieved by
/// using `#[derive(PartialEq, Eq, Hash)]`. If you implement these yourself, it
/// is important that the following property holds:
///
/// ```text
/// e1 == e2 -> hash(e1) == hash(e2)
/// ```
///
/// In other words, if two elements are equal, their hashes must also be equal.
///
/// It is a logic error for an item to be modified in such a way that the item's
/// hash, as determined by the [`Hash`] trait, or its equality, as determined by
/// the [`Eq`] trait, changes while it is in the multiset. This is normally only
/// possible through [`Cell`], [`RefCell`], global state, I/O, or unsafe code.
///
/// In addition to these constraints, elements must implement the [`Clone`]
/// trait. As above, this can frequently be derived using `#[derive(Clone)]` or
/// adding the `Clone` trait to the other traits in an existing `#derive[...]`
/// macro. A multiset stores the first element inserted with and a `usize`. When
/// an api call returns one or more elements it will return clones of that
/// initial element. For complex elements this can sometimes lead to unexpected
/// behavior, and in those cases it may be preferable to explore other hash
/// functions or non-hash map backed multiset implementations.
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
/// bag.insert("contemplate");
/// bag.insert("the");
/// bag.insert("variations");
/// bag.insert("of");
/// bag.insert("the");
/// bag.insert("23");
/// bag.insert("letters");
///
/// // Check for a specific one.
/// if !bag.contains(&"Hacedor") {
///     println!("We have {} words, but Hacedor ain't one.",
///              bag.distinct_elements().len());
/// }
///
/// // Remove a word
/// bag.remove(&"23");
///
/// // Iterate over everything.
/// for (word, count) in &bag {
///     println!("{}: {}", word, count);
/// }
/// ```
///
/// The easiest way to use `MultiSet` with a custom type is to derive [`Eq`],
/// [`Hash`], and [`Clone`]. We must also derive [`PartialEq`], this will in
/// the future be implied by [`Eq`].
///
/// ```
/// use mset::MultiSet;
/// #[derive(Hash, Eq, PartialEq, Debug, Clone)]
/// struct GuineaPig {
///     name: String,
///     weight: usize,
/// }
///
/// let mut gps = MultiSet::new();
///
/// gps.insert(GuineaPig { name: String::from("Mumpkans"), weight: 8 });
/// gps.insert(GuineaPig { name: String::from("Mumpkans"), weight: 8 });
/// gps.insert(GuineaPig { name: String::from("Mr. Mister"), weight: 5 });
/// gps.insert(GuineaPig { name: String::from("Popchop"), weight: 12 });
/// gps.insert(GuineaPig { name: String::from("Fuzzable"), weight: 9 });
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
///     ["Deathmlom", "Bun Roy", "Funbees", "Sporky", "Bun Roy"].iter().copied().collect();
/// // use the values stored in the multiset
/// ```
///
/// [`Cell`]: struct.Cell.html
/// [`Eq`]: trait.Eq.html
/// [`Hash`]: trait.Hash.html
/// [`Clone`]: https://doc.rust-lang.org/std/clone/trait.Clone.html
/// [`HashMap`]: struct.HashMap.html
/// [`PartialEq`]: trait.PartialEq.html
/// [`RefCell`]: struct.RefCell.html
#[derive(Clone)]
pub struct MultiSet<T, S = RandomState> {
    // MultiSet element counts are strictly positive integers
    elem_counts: HashMap<T, usize, S>,
}

impl<T> MultiSet<T, RandomState> {
    /// Create an empty `MultiSet`.
    ///
    /// The multiset is initially created with a capacity of 0 distinct
    /// elements, so it will not allocate until it is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mset: MultiSet<char> = MultiSet::new();
    /// assert_eq!(mset.len(), 0);
    /// assert_eq!(mset.distinct_elements().len(), 0);
    /// ```
    pub fn new() -> MultiSet<T, RandomState> {
        MultiSet {
            elem_counts: HashMap::new(),
        }
    }

    /// Create an empty `MultiSet` with the specified capacity.
    ///
    /// The multiset will be able to hold at least `capacity` distinct elements
    /// without reallocating. If `capacity` is 0, the multiset will not allocate
    /// on creation.
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
    /// Returns the number of distinct elements the multiset can hold without
    /// reallocating.
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

    /// An iterator visiting all distinct elements and counts in arbitrary order.
    /// The iterator element type is `(&T, &usize)`.
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
    pub fn element_counts(&self) -> ElementCounts<T> {
        ElementCounts {
            iter: self.elem_counts.iter(),
        }
    }

    /// An iterator visiting all distinct elements in arbitrary order.
    /// The iterator element type is `&'a T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// mset.insert('a');
    /// mset.insert('a');
    /// mset.insert('b');
    /// mset.insert('c');
    ///
    /// // Will print in an arbitrary order.
    /// for e in mset.distinct_elements() {
    ///     println!("{}", e);
    /// }
    /// ```
    pub fn distinct_elements(&self) -> Elements<T> {
        self.elem_counts.keys()
    }

    /// Returns the total number of elements in the multiset.
    ///
    /// This is dynamically computed and runs in O(N) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// assert_eq!(mset.len(), 0);
    ///
    /// mset.insert_times('a', 10);
    /// mset.insert('b');
    /// mset.insert('b');
    ///
    /// assert_eq!(mset.len(), 12);
    /// ```
    pub fn len(&self) -> usize {
        self.elem_counts.values().sum()
    }

    /// Returns `true` if the multiset contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// assert!(mset.is_empty());
    ///
    /// mset.insert('L');
    ///
    /// assert!(!mset.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elem_counts.is_empty()
    }

    /// Clears the multiset, removing all values.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    ///
    /// mset.insert('v');
    ///
    /// assert_eq!(mset.is_empty(), false);
    ///
    /// mset.clear();
    ///
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

    /// Create an empty `MultiSet` with the specified capacity, using
    /// `hash_builder` to hash the elements.
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
    /// let mset: MultiSet<char> = MultiSet::with_hasher(hasher);
    /// let hasher: &RandomState = mset.hasher();
    /// ```
    pub fn hasher(&self) -> &S {
        self.elem_counts.hasher()
    }

    /// Reserves capacity for at least `additional` more distinct elements to
    /// be inserted in the `HashMap`. The collection may reserve more space to avoid
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
    /// let mut mset: MultiSet<usize> = MultiSet::new();
    /// mset.reserve(10);
    /// ```
    pub fn reserve(&mut self, additional: usize) {
        self.elem_counts.reserve(additional)
    }

    /// Shrinks the capacity of the multiset as much as possible. It will
    /// drop down while maintaining the internal rules and possibly leaving
    /// some space in accordance with the resize policy.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::with_capacity(100);
    /// mset.insert(1);
    /// mset.insert(2);
    ///
    /// assert!(mset.capacity() >= 100);
    ///
    /// mset.shrink_to_fit();
    ///
    /// assert!(mset.capacity() >= 2);
    /// ```
    pub fn shrink_to_fit(&mut self) {
        self.elem_counts.shrink_to_fit();
    }

    /// An iterator visiting all distinct elements and counts in arbitrary order.
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

    /// An iterator visiting all elements in arbtitrary order.
    /// The iterator element type is `T`
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let mut mset = MultiSet::new();
    /// mset.insert("a");
    /// mset.insert("a");
    /// mset.insert("b");
    ///
    /// for elem in mset.iter_with_multiplicity() {
    ///     println!("{}", elem);
    /// }
    /// ```
    pub fn iter_with_multiplicity(&self) -> impl Iterator<Item = T> + '_
    where
        T: Clone,
    {
        self.iter()
            .flat_map(|(el, cnt)| std::iter::repeat_with(move || el.clone()).take(*cnt))
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
        match self.len() < other.len() {
            true => self.iter().all(|(e, _)| !other.contains(e)),
            false => other.iter().all(|(e, _)| !self.contains(e)),
        }
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
        self.iter()
            .all(|(e, m)| *m <= other.get(e).unwrap_or_default())
    }

    /// Returns `true` if the multiset is a superset of another,
    /// i.e., `self` contains at least all the values in `other`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let msub: MultiSet<_> = [1, 2, 2].iter().copied().collect();
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

    /// Add a value to the multiset.
    ///
    /// If the multiset did not have this value present, `true` is returned.
    ///
    /// If the multiset did have this value present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// assert_eq!(mset.insert('a'), true);
    /// assert_eq!(mset.insert('a'), false);
    ///
    /// assert_eq!(mset.len(), 2);
    /// assert_eq!(mset.distinct_elements().len(), 1);
    /// ```
    pub fn insert(&mut self, value: T) -> bool {
        self.insert_times(value, 1)
    }

    /// Add a value to the multiset some number of times
    ///
    /// If the multiset did not have this value present, `true` is returned.
    ///
    /// If the multiset did have this value present, `false` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// assert!(mset.insert_times('a', 10));
    /// assert!(!mset.insert_times('a', 2));
    ///
    /// assert_eq!(mset.distinct_elements().len(), 1);
    /// assert_eq!(mset.len(), 12);
    /// assert_eq!(mset.get(&'a'), Some(12));
    /// ```
    pub fn insert_times(&mut self, value: T, multiplicity: usize) -> bool {
        match self.elem_counts.entry(value) {
            Entry::Vacant(view) => {
                view.insert(multiplicity);
                true
            }
            Entry::Occupied(mut view) => {
                *view.get_mut() += multiplicity;
                false
            }
        }
    }

    /// Remove a value from the multiset. Returns whether the value was
    /// present in the multiset.
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// assert_eq!(mset.len(), 0);
    /// mset.insert('a');
    ///
    /// mset.shrink_to_fit();
    /// assert_eq!(mset.len(), 1);
    /// assert_eq!(mset.remove(&'a'), true);
    /// assert_eq!(mset.remove(&'a'), false);
    ///
    /// mset.shrink_to_fit();
    ///
    /// assert_eq!(mset.capacity(), 0);
    /// ```
    pub fn remove<Q: ?Sized>(&mut self, element: &Q) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.remove_times(element, 1)
    }

    /// Remove multiple values from the multiset. Returns whether the values
    /// were present in the multiset.
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// mset.insert_times('c', 10);
    ///
    /// assert_eq!(mset.remove_times(&'c', 2), true);
    /// assert_eq!(mset.remove_times(&'c', 10), false);
    /// assert_eq!(mset.len(), 0);
    ///
    /// assert!(mset.is_empty());
    /// ```
    pub fn remove_times<Q: ?Sized>(&mut self, element: &Q, multiplicity: usize) -> bool
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        let default_value = &mut 0;
        let value = self.elem_counts.get_mut(element).unwrap_or(default_value);

        // exactly enough elements
        if *value == multiplicity {
            self.elem_counts.remove(element);
            return true;
        }

        *value = value.saturating_sub(multiplicity);

        // insufficient elements
        if *value == 0 {
            self.elem_counts.remove(element);
            return false;
        }

        // more than enough elements
        true
    }

    /// Removes all instances of an element from the multiset and returns the
    /// multiplicity, if the element is in the multiset.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = vec!['a', 'b', 'c', 'b', 'a'].iter().cloned().collect();
    /// assert_eq!(mset.take(&'b'), Some(('b', 2)));
    /// assert_eq!(mset.take(&'d'), None);
    /// ```
    ///
    /// [`Eq`]: trait.Eq.html
    /// [`Hash`]: trait.Hash.html
    pub fn take(&mut self, value: &T) -> Option<(T, usize)> {
        self.elem_counts.remove_entry(value)
    }

    /// Retains only the elements specified by the predicate.
    ///
    /// In other words, remove all pairs `(elem, multiplicty)` such that
    /// `f(&k, usize)` returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = vec!['a', 'b', 'c', 'b', 'a'].iter().cloned().collect();
    /// mset.retain(|_, m: usize| m % 2 == 0);
    ///
    /// assert_eq!(mset.distinct_elements().len(), 2);
    /// assert_eq!(mset.len(), 4);
    /// ```
    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&T, usize) -> bool,
    {
        self.elem_counts.retain(|e, m| f(e, *m));
    }

    /// Clears the multiset, returning all elements in an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
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
            curr: None,
            remaining: 0,
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
            other,
            curr: None,
            remaining: 0,
        }
    }

    /// Visits the values representing the union, i.e., all the values in `self`
    /// or `other`.
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
            curr: None,
            remaining: 0,
        }
    }

    /// Returns `true` if the multiset contains a value.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
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

    /// Returns a usize representing how many of the provided element are
    /// stored in the mset.
    ///
    /// Multiplicty is represented as a usize but `0` is an invalid value and
    /// `Size(0)` is an invalid return value. Expect None instead.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// mset.insert('a');
    ///
    /// assert_eq!(mset.get(&'a'), Some(1));
    /// assert_eq!(mset.get(&'b'), None);
    /// ```
    pub fn get<Q: ?Sized>(&self, element: &Q) -> Option<usize>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.get(element).copied()
    }

    /// Returns the element-multiplicity pair corresponding to the supplied
    /// element.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset: MultiSet<_> = MultiSet::new();
    /// mset.insert('a');
    ///
    /// assert_eq!(mset.get_element_multiplicity(&'a'), Some((&'a', &1)));
    /// assert_eq!(mset.get_element_multiplicity(&'b'), None);
    /// ```
    pub fn get_element_multiplicity<Q: ?Sized>(&self, element: &Q) -> Option<(&T, &usize)>
    where
        T: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.elem_counts.get_key_value(element)
    }
}

/// Create a `MultiSet` from a `HashMap<T, usize>`.
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
/// let mset: MultiSet<_> = MultiSet::from(m);
///
/// assert_eq!(mset.distinct_elements().len(), 2);
/// assert_eq!(mset.len(), 5);
/// ```
impl<T: Hash + Eq> From<HashMap<T, usize>> for MultiSet<T> {
    fn from(map: HashMap<T, usize>) -> Self {
        Self { elem_counts: map }
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

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> ops::BitOr<&MultiSet<T, S>>
    for &MultiSet<T, S>
{
    type Output = MultiSet<T, S>;

    /// Returns the union of `self` and `rhs` (right hand side) as a new
    /// `MultiSet<T, S>`.
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
    /// let expected = [1, 2, 3, 3, 3, 3, 4, 5];
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

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> ops::BitAnd<&MultiSet<T, S>>
    for &MultiSet<T, S>
{
    type Output = MultiSet<T, S>;

    /// Returns the intersection of `self` and `rhs` (right hand side) as a new
    /// `MultiSet<T, S>`.
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

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> ops::BitXor<&MultiSet<T, S>>
    for &MultiSet<T, S>
{
    type Output = MultiSet<T, S>;

    /// Returns the symmetric difference of `self` and `rhs` (right hand side)
    /// as a new `MultiSet<T, S>`.
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

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> ops::Sub<&MultiSet<T, S>> for &MultiSet<T, S> {
    type Output = MultiSet<T, S>;

    /// Returns the difference of `self` and `rhs` (right hand side) as a new
    /// `MultiSet<T, S>`.
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

impl<T: Eq + Hash + Clone, S: BuildHasher> PartialEq for MultiSet<T, S> {
    fn eq(&self, other: &MultiSet<T, S>) -> bool {
        self.len() == other.len()
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher> Eq for MultiSet<T, S> {}

impl<T: Eq + Hash + fmt::Debug + Clone, S: BuildHasher> fmt::Debug for MultiSet<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.element_counts()).finish()
    }
}

impl<T: Hash + Eq + Clone, S: BuildHasher + Default> FromIterator<T> for MultiSet<T, S> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> MultiSet<T, S> {
        let iter = iter.into_iter();
        let mut mset: MultiSet<T, S> = MultiSet::with_hasher(Default::default());
        for key in iter {
            mset.insert(key);
        }
        mset
    }
}

impl<T: Hash + Eq + Clone, S: BuildHasher + Default> FromIterator<(T, usize)> for MultiSet<T, S> {
    fn from_iter<I: IntoIterator<Item = (T, usize)>>(iter: I) -> MultiSet<T, S> {
        let mut mset = MultiSet::with_hasher(Default::default());
        mset.extend(iter);
        mset
    }
}

impl<T: Hash + Eq + Clone, S: BuildHasher + Default> IntoIterator for MultiSet<T, S> {
    type Item = (T, usize);
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            iter: self.elem_counts.into_iter(),
        }
    }
}

impl<'a, T: Hash + Eq + Clone, S: BuildHasher> IntoIterator for &'a MultiSet<T, S> {
    type Item = (&'a T, &'a usize);
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> <Self as IntoIterator>::IntoIter {
        self.iter()
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher> Extend<(T, usize)> for MultiSet<T, S> {
    fn extend<I: IntoIterator<Item = (T, usize)>>(&mut self, iter: I) {
        for (key, value) in iter.into_iter() {
            self.insert_times(key, value);
        }
    }
}

impl<'a, T: Eq + Hash + Clone, S: BuildHasher> Extend<(&'a T, &'a usize)> for MultiSet<T, S> {
    fn extend<I: IntoIterator<Item = (&'a T, &'a usize)>>(&mut self, iter: I) {
        for (key, value) in iter.into_iter().map(|(k, v)| ((*k).clone(), (*v))) {
            self.insert_times(key, value);
        }
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher + Default> Extend<T> for MultiSet<T, S> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for key in iter.into_iter() {
            self.insert(key);
        }
    }
}

impl<'a, T: Eq + Hash + Clone, S: BuildHasher + Default> Extend<&'a T> for MultiSet<T, S> {
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        for key in iter.into_iter().map(|k| (*k).clone()) {
            self.insert(key.clone());
        }
    }
}

/// An iterator over the element counts of a `MultiSet`.
///
/// This `struct` is created by the [`element_counts`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`element_counts`]: struct.MultiSet.html#method.element_counts
#[derive(Debug)]
pub struct ElementCounts<'a, T: 'a> {
    iter: hash_map::Iter<'a, T, usize>,
}

impl<T> Clone for ElementCounts<'_, T> {
    fn clone(&self) -> Self {
        ElementCounts {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T> Iterator for ElementCounts<'a, T> {
    type Item = (&'a T, &'a usize);

    fn next(&mut self) -> Option<(&'a T, &'a usize)> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for ElementCounts<'_, T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> FusedIterator for ElementCounts<'_, T> {}

/// An iterator over the elements of a `MultiSet`.
///
/// This `struct` is created by the [`elements`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`distinct_elements`]: struct.MultiSet.html#method.distinct_elements
pub type Elements<'a, T> = std::collections::hash_map::Keys<'a, T, usize>;

/// An iterator over the items of a `MultiSet`.
///
/// This `struct` is created by the [`iter`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`iter`]: struct.MultiSet.html#method.iter
#[derive(Debug)]
pub struct Iter<'a, T: 'a> {
    iter: hash_map::Iter<'a, T, usize>,
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

/// An owning iterator over the items of a `MultiSet`.
///
/// This `struct` is created by the [`into_iter`] method on [`MultiSet`]
/// (provided by the `IntoIterator` trait). See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`into_iter`]: struct.MultiSet.html#method.into_iter
#[derive(Debug)]
pub struct IntoIter<T> {
    iter: hash_map::IntoIter<T, usize>,
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

#[derive(Debug)]
pub struct Drain<'a, T: 'a> {
    iter: hash_map::Drain<'a, T, usize>,
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
    // iterator of the first mset
    iter: Iter<'a, T>,
    // the second mset
    other: &'a MultiSet<T, S>,
    curr: Option<&'a T>,
    remaining: usize,
}

impl<T: Clone, S> Clone for Intersection<'_, T, S> {
    fn clone(&self) -> Self {
        Intersection {
            iter: self.iter.clone(),
            curr: self.curr,
            ..*self
        }
    }
}

impl<'a, T: Eq + Hash + Clone, S: BuildHasher> Iterator for Intersection<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            match self.remaining {
                0 => {} // do nothing
                _ => {
                    self.remaining -= 1;
                    return self.curr;
                }
            }

            let (elem, count) = self.iter.next()?;
            let other_count = self.other.get(elem).unwrap_or(0usize);

            self.curr = Some(elem);
            self.remaining = min(*count, other_count);
        }
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher> FusedIterator for Intersection<'_, T, S> {}

impl<T: fmt::Debug + Eq + Hash + Clone, S: BuildHasher> fmt::Debug for Intersection<'_, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the difference of `MultiSet`s.
///
/// This `struct` is created by the [`difference`] method on [`MultiSet`].
/// See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`difference`]: struct.MultiSet.html#method.difference
pub struct Difference<'a, T, S> {
    // iterator of the first mset
    iter: Iter<'a, T>,
    // the second mset
    other: &'a MultiSet<T, S>,
    curr: Option<&'a T>,
    remaining: usize,
}

impl<T: Clone, S> Clone for Difference<'_, T, S> {
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
            match self.remaining {
                0 => {} // do nothing
                _ => {
                    self.remaining -= 1;
                    return self.curr;
                }
            }

            let (elem, count) = self.iter.next()?;
            let other_count = self.other.get(elem).unwrap_or(0usize);

            self.curr = Some(elem);
            self.remaining = count.saturating_sub(other_count);
        }
    }
}

impl<T: Eq + Hash + Clone, S: BuildHasher> FusedIterator for Difference<'_, T, S> {}

impl<T: fmt::Debug + Eq + Hash + Clone, S: BuildHasher> fmt::Debug for Difference<'_, T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}

/// A lazy iterator producing elements in the symmetric difference of
/// `MultiSet`s.
///
/// This `struct` is created by the [`symmetric_difference`] method on
/// [`MultiSet`]. See its documentation for more.
///
/// [`MultiSet`]: struct.MultiSet.html
/// [`symmetric_difference`]: struct.MultiSet.html#method.symmetric_difference
pub struct SymmetricDifference<'a, T: 'a, S: 'a> {
    iter: Chain<Difference<'a, T, S>, Difference<'a, T, S>>,
}

impl<T: Clone, S> Clone for SymmetricDifference<'_, T, S> {
    fn clone(&self) -> Self {
        SymmetricDifference {
            iter: self.iter.clone(),
        }
    }
}

impl<'a, T: Eq + Hash + Clone, S: BuildHasher> Iterator for SymmetricDifference<'a, T, S> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.iter.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T: fmt::Debug + Eq + Hash + Clone, S: BuildHasher> fmt::Debug
    for SymmetricDifference<'_, T, S>
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
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
    curr: Option<&'a T>,
    remaining: usize,
}

impl<T: Clone> Clone for Union<'_, T> {
    fn clone(&self) -> Self {
        Union {
            iter: self.iter.clone(),
            ..*self
        }
    }
}

impl<T: Eq + Hash + Clone> FusedIterator for Union<'_, T> {}

impl<'a, T: Eq + Hash + Clone> Iterator for Union<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        loop {
            match self.remaining {
                0 => {} // do nothing
                _ => {
                    self.remaining -= 1;
                    return self.curr;
                }
            }

            let (elem, count) = self.iter.next()?;

            self.curr = Some(elem);
            self.remaining = *count;
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T: fmt::Debug + Eq + Hash + Clone> fmt::Debug for Union<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.clone()).finish()
    }
}
