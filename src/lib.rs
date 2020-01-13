
use std::borrow::Borrow;
use std::collections::hash_map::{Entry, Keys, Values, ValuesMut};
use std::collections::HashMap;
use std::collections::hash_map::RandomState;
use std::default::Default;
use std::hash::{BuildHasher, Hash};

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct MultiSet<K, S = RandomState>
where
    K: Hash + Eq,
    S: BuildHasher
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
    pub fn new() -> MultiSet<K, S> where S: Default {
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
    /// assert!(set.capacity() >= 10);
    /// ```
    pub fn with_capacity(capacity: usize) -> MultiSet<K, S> where S: Default {
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

    /// Creat a `MultiSet` with the same BuildHasher type.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// use std::collections::HashMap;
    ///
    /// let mut m = HashMap::new();
    /// m.insert_times('a', 4);
    /// m.insert_times('z', 1);
    ///
    /// let mset = Multiset::from_hashmap(m);
    /// assert_eq!(c.len(), 2);
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
    /// let mset: MultiSet<i32> = MultiSet::with_capacity(100);
    /// assert!(mset.capacity >= 100);
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
    /// use mut mset = MultiSet::new();
    /// mset.insert('a');
    /// mset.insert('a');
    /// mset.insert('b');
    /// mset.insert('c');
    ///
    /// // Will print in an arbitrary order.
    /// for key in set.keys() {
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
    /// use mut mset = MultiSet::new();
    /// mset.insert('a');
    /// mset.insert('a');
    /// mset.insert('b');
    /// mset.insert('c');
    ///
    /// // Will print in an arbitrary order.
    /// for val in set.values() {
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
    /// let mut mset = MultiSet::new();
    ///
    /// mset.insert_times("a", 1);
    /// mset.insert_times("b", 2);
    /// mset.insert_times("c", 3);
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
    /// let mut a = MultiSet::new();
    /// assert_eq!(a.len(), 0);
    /// a.insert('a', 10);
    /// assert_eq!(a.len(), 1);
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
    /// let mut mset = MultiSet::new();
    /// assert!(mset.is_empty());
    /// mset.insert(l);
    /// assert!(!mset.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.elem_counts.is_empty()
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
    /// let mut mset = MultiSet::new();
    ///
    /// assert!(set.insert('a'));
    /// assert!(!set.insert('a'));
    /// assert_eq!(set.len(), 1);
    /// ```
    pub fn insert(&mut self, value: K) -> bool {
        self.insert_times(value, 1)
    }

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
    /// use msets::MultiSet;
    ///
    /// let mut mset = MultiSet::new();
    /// mset.insert("a");
    /// assert_eq!(map.get(&"a"), Some(&1));
    /// assert_eq!(map.get(&"b"), None);
    /// ```
    pub fn get(&self, key: &K) -> Option<&usize>
    where
        K: Borrow<K>,
    {
        self.elem_counts.get(key)
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
    /// use msets::MultiSet
    ///
    /// let mut mset = MutliSet::new();
    /// mset.insert("a");
    /// assert_eq!(mset.get_key_value(&"a"), Some((&"a", &1)));
    /// assert_eq!(mset.get_key_value(&"b"), None);
    /// ```
    pub fn get_key_value(&self, key: &usize) -> Option<(&K, &usize)>
    where
        K: Borrow<usize>,
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

    // #[test]
    // fn test_combine_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.insert('a');
    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     m2.insert('b', 10);

    //     let mut m3: MultiSet<char> = m1.combine(m2);
    //     assert_eq!(m3.get('a'), 1);
    //     assert_eq!(m3.get('b'), 10);
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

    // #[test]
    // fn test_retrieving_mset_values() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.insert("dragons", 9);

    //     assert_eq!(m1.get("dragons"), Some(9));
    //     assert_eq!(m1.get("unicorns"), None);
    // }

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

    // #[tests]
    // fn test_mset_deletion() {
    //     let mut mset: MultiSet<char> = MultiSet::new();

    //     assert!(mset.is_empty());

    //     mset.insert('c', 3);

    //     assert!(!mset.is_empty());

    //     assert_eq!(mset.get('c').some(), 3);

    //     mset.clear();

    //     assert!(mset.is_empty());
    // }

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
