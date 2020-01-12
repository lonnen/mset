use std::collections::hash_map::{Iter as HashMapIter, IterMut as HashMapIterMut};
use std::collections::HashMap;
use std::hash::Hash;

/// The easiest way to use `HashMap` with a custom key type is to derive [`Eq`] and [`Hash`].
/// let timber_resources: HashMap<&str, i32> = [("Norway", 100), ("Denmark", 50), ("Iceland", 10)]
#[derive(Clone)]
pub struct MultiSet<K, V> {
    elem_counts: HashMap<K, V>,
}

impl<K: Hash + Eq, V> MultiSet<K, V> {
    /// Create an empty `MultiSet`.
    ///
    ///
    /// The multi set is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    /// let mset: MultiSet<char> = MultiSet::new();
    /// ```
    pub fn new() -> MultiSet<K, V> {
        MultiSet {
            elem_counts: HashMap::new(),
        }
    }

    /// Create an empty `MultiSet`  with the specified capacity.
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
    pub fn with_capacity(capacity: usize) -> MultiSet<K, V> {
        MultiSet {
            elem_counts: HashMap::with_capacity(capacity),
        }
    }
}

impl<K, V> MultiSet<K, V> {
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

    /// An iterator visiting all keys in arbitrary order.
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
    /// for key in set.iter() {
    ///     println!("{}", key);
    /// }
    /// ```
    pub fn keys(&self) -> Keys<'_, K, V> {
        Keys {
            inner: self.iter(),
        }
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
    pub fn values(&self) -> Values<'_, K, V> {
        Values {
            inner: self.iter(),
        }
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
    /// mset.insert("a", 1);
    /// mset.insert("b", 2);
    /// mset.insert("c", 3);
    ///
    /// for val in mset.values_mut() {
    ///     *val = *val + 10;
    /// }
    ///
    /// for val in mset.values() {
    ///     println!("{}", val);
    /// }
    /// ```
    pub fn values_mut(&mut self) -> ValuesMut<'_, K, V> {
        ValuesMut { inner: self.elem_counts.iter_mut() }
    }

    /// An iterator visiting all key-value pairs in arbitrary order.
    /// The iterator element type is `(&'a K, &'a V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// let mut mset = MultiSet::new();
    ///
    /// mset.insert("a", 1);
    /// mset.insert("b", 2);
    /// mset.insert("c", 3);
    ///
    /// for val in mset.iter() {
    ///     println!("key: {}, val: {}", key, val);
    /// }
    /// ```
    pub fn iter(&self) -> Iter<'_, K, V> {
        Iter { base: self.elem_counts.iter() }
    }

    /// An iterator visiting all values mutably in arbitrary order,
    /// with mutable references to the values.
    /// The iterator element type is `(&'a K, &'a mut V)`.
    ///
    /// # Examples
    ///
    /// ```
    /// use mset::MultiSet;
    ///
    /// let mut mset = MultiSet::new();
    ///
    /// mset.insert("a", 1);
    /// mset.insert("b", 2);
    /// mset.insert("c", 3);
    ///
    /// for (_, val) in mset.iter_mut() {
    ///     *val *= 10;
    /// }
    ///
    /// for val in mset.iter() {
    ///     println!("key: {}, val: {}", key, val);
    /// }
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, K, V> {
        IterMut { base: self.elem_counts.iter_mut() }
    }

    pub fn len(&self) -> usize {
        self.elem_counts.len()
    }

}

impl<K, V> PartialEq for MultiSet<K, V>
where
    K: Eq + Hash,
{
    fn eq(&self, other: &MultiSet<K, V>) -> bool {
        return true;
    }
}

impl<K, V> Eq for MultiSet<K, V> where K: Eq + Hash {}
/// An iterator over the entries of a `MultiSet`.
///
/// This `struct` is created by the [`iter`] method on [`MultiSet`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.MultiSet.html#method.iter
/// [`MultiSet`]: struct.MultiSet.html
#[derive(Clone, Debug)]
pub struct Iter<'a, K: 'a, V: 'a> {
    base: HashMapIter<'a, K, V>,
}

/// A mutable iterator over the entries of a `MultiSet`.
///
/// This `struct` is created by the [`iter_mut`] method on [`MultiSet`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.MultiSet.html#method.iter_mut
/// [`MultiSet`]: struct.MultiSet.html
#[derive(Debug)]
pub struct IterMut<'a, K: 'a, V: 'a> {
    base: HashMapIterMut<'a, K, V>,
}

/// An iterator over the keys of a `MultiSet`.
///
/// This `struct` is created by the [`keys`] method on [`Multiset`]. See its
/// documentation for more.
///
/// Identical to the HashMultiSet Keys struct, but reimplemented here to work
/// around `inner` being an inaccesible private field.
///
/// [`keys`]: struct.MultiSet.html#method.keys
/// [`MultiSet`]: struct.MultiSet.html
#[derive(Clone, Debug)]
pub struct Keys<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

/// This `struct` is created by the [`values`] method on [`Multiset`]. See its
/// documentation for more.
///
/// Identical to the HashMultiSet Values struct, but reimplemented here to work
/// around `inner` being an inaccesible private field.
///
/// [`values`]: struct.MultiSet.html#method.values
/// [`MultiSet`]: struct.MultiSet.html
#[derive(Clone, Debug)]
pub struct Values<'a, K: 'a, V: 'a> {
    inner: Iter<'a, K, V>,
}

// FIXME Drain

/// A mutable iterator over the values of a `MultiSet`.
///
/// This `struct` is created by the [`values_mut`] method on [`MultiSet`]. See its
/// documentation for more.
///
/// [`values_mut`]: struct.MultiSet.html#method.values_mut
/// [`MultiSet`]: struct.MultiSet.html
#[derive(Debug)]
pub struct ValuesMut<'a, K: 'a, V: 'a> {
    inner: HashMapIterMut<'a, K, V>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_new_msets() {
        let mset: MultiSet<char, usize> = MultiSet::new();
    }

    // #[test]
    // fn test_add_and_retrieve_elements() {
    //     let mut mset: MultiSet<char> = MultiSet::new();
    //     mset.add('a');
    //     assert_eq!(mset.get('a'), 1);
    //     mset.add('a');
    //     assert_eq!(mset.get('a'), 2);

    //     mset.insert('b', 5);
    //     assert_eq!(mset.get('b'), 5);
    // }

    // #[test]
    // fn test_combine_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     m1.add('a');
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
    //         mset.add(c);
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
    //         mset.add(c);
    //     }

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     let v2: Vec<char> = vec!['a', 'a', 'a', 'c'];

    //     for c in v3 {
    //         mset.add(c);
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
    //         m1.add(c);
    //         m2.add(c);
    //         m2.add(c);
    //     }

    //     assert_eq!(m1.times(2), m2);
    // }

    // #[tests]
    // fn test_union_of_msets() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     let mut m2: MultiSet<char> = MultiSet::new();

    //     for c in vec!['a', 'a', 'b'] {
    //         m1.add(c);
    //     }

    //     for c in vec!['a', 'a', 'b'] {
    //         m2.add(c);
    //     }

    //     let mut m3: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'a', 'b'] {
    //         m3.add(c);
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
    //         m1.add(c);
    //     }

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'b', 'd'] {
    //         m2.add(c);
    //     }

    //     let mut m3: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'b', 'b', 'c'] {
    //         m3.add(c);
    //     }

    //     assert_eq!(m1.difference_update(m2), m3);
    // }

    // #[tests]
    // fn test_discard() {
    //     let mut mset: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b', 'b', 'b', 'c'] {
    //         mset.add(c);
    //     }

    //     mset.discard('b');

    //     let mut expected: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'c'] {
    //         mset.add(c);
    //     }

    //     assert_eq!(mset, expected);
    // }

    // #[tests]
    // fn test_intersection_update() {
    //     let mut m1: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b'] {
    //         m1.add(c);
    //     }

    //     let mut m2: MultiSet<char> = MultiSet::new();
    //     for c in vec!['b', 'c'] {
    //         m2.add(c);
    //     }

    //     let mut expected: MultiSet<char> = MultiSet::new();
    //     for c in vec!['b'] {
    //         mset.add(c);
    //     }

    //     m1.intersection_update(m2);
    //     assert_eq!(m1, expected);
    // }

    // #[tests]
    // fn test_pop() {
    //     let mut mset: MultiSet<char> = MultiSet::new();
    //     for c in vec!['a', 'a', 'b'] {
    //         mset.add(c);
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
