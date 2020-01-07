use std::collections::HashMap;
use std::hash::Hash;

#[derive(Clone, Default, Eq)]
pub struct MultiSet<K>
where
    K: Eq + Hash,
{
    elem_counts: HashMap<K, usize>,
    size: usize,
}

impl<K> MultiSet<K>
where
    K: Eq + Hash,
{
    pub fn new() -> Self {
        MultiSet {
            elem_counts: HashMap::new(),
            size: 0,
        }
    }
}

impl<K> PartialEq for MultiSet<K>
where
    K: Eq + Hash,
{
    fn eq(&self, other: &MultiSet<K>) -> bool {
        // TODO: Fix this
        return true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_create_new_msets() {
        let mset: MultiSet<char> = MultiSet::new();
    }

    #[test]
    fn test_add_and_retrieve_elements() {
        let mut mset: MultiSet<char> = MultiSet::new();
        mset.add('a');
        assert_eq!(mset.get('a'), 1);
        mset.add('a');
        assert_eq!(mset.get('a'), 2);

        mset.insert('b', 5);
        assert_eq!(mset.get('b'), 5);
    }

    #[test]
    fn test_combine_msets() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.add('a');
        let mut m2: MultiSet<char> = MultiSet::new();
        m2.insert('b', 10);

        let mut m3: MultiSet<char> = m1.combine(m2);
        assert_eq!(m3.get('a'), 1);
        assert_eq!(m3.get('b'), 10);
    }

    // #[test]
    // fn copy_msets(){ }

    #[test]
    fn test_mset_difference() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert('a', 3);
        m1.insert('c', 5);

        let mut m2: MultiSet<char> = MultiSet::new();
        m2.insert('a', 1);
        ms.insert('b', 1);

        let m1d2: MultiSet<char> = m1.difference(m2);
        assert_eq!(m1d2.get('a'), Some(2));
        assert_eq!(m1d2.get('c'), Some(5));

        let m2d1: MultiSet<char> = m2.difference(m1);
        assert_eq!(m2d1.get('b'), Some(1));
    }

    #[test]
    fn test_difference_update() {
        return true; // TODO mod in place
    }

    #[test]
    fn test_retrieving_mset_values() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert("dragons", 9);

        assert_eq!(m1.get("dragons"), Some(9));
        assert_eq!(m1.get("unicorns"), None);
    }

    #[test]
    fn test_intersection_of_msets() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert('a', 2);

        let mut m2: MultiSet<char> = MultiSet::new();
        m2.insert('a', 1);
        m2.insert('b', 3);

        let m3: MultiSet<char> = m1.intersection(m2);
        let m4: MultiSet<char> = m2.intersection(m1);
        assert_eq!(m3, m4);
        assert_eq!(m3.get('a'), Some(1));
    }

    #[test]
    fn test_msets_within_msets() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert('a', 2);

        let mut m2: MultiSet<char> = MultiSet::new();
        m2.insert('a', 1);
        m2.insert('b', 3);

        let mut m3: MultiSet<char> = MultiSet::new();
        m3.insert('a', 1);

        let mut m4: MultiSet<char> = MultiSet::new();
        m4.insert('x', 777);

        // some overlapping elements
        assert!(!m1.is_disjoint(m2));
        assert!(!m1.is_disjoint(m3));

        assert!(!m1.is_subset(m2));
        assert!(!m1.is_subset(m3));

        assert!(!m1.is_superset(m2));
        assert!(!m1.is_superset(m3));

        // no overlap at all
        assert!(m1.is_disjoint(m4));

        // is_disjoint is symmetric
        assert!(!m2.is_disjoint(m1));
        assert!(!m3.is_disjoint(m1));
        assert!(m4.is_disjoint(m1));

        // one contained within another
        assert!(m3.is_subset(m1));
        assert!(m3.is_subset(m2));

        assert!(m1.is_superset(m3));
        assert!(m2.is_superset(m3));

        // is_subset and is_superset are symmetric to one another
        assert!(m1.is_superset(m3));
        assert!(m2.is_superset(m3));

        assert!(m3.is_subset(m1));
        assert!(m3.is_subset(m1));
    }

    #[test]
    fn test_ways_to_retrieve_the_contents_of_an_mset() {
        let mut mset: MultiSet<char> = MultiSet::new();

        let v1: Vec<char> = vec!['a', 'b', 'b', 'c', 'c', 'c'];

        for c in v1 {
            mset.add(c);
        }

        let keys = mset.distinct_elements();
        assert_eq!(keys.len(), 3);
        assert!(keys.contains('a'));
        assert!(keys.contains('b'));
        assert!(keys.contains('c'));

        let counts = mset.multiplicites();
        assert_eq!(counts.len(), 3);

        let mut observed: usize = 0;
        for i in items {
            observed += i;
        }
        assert_eq!(observed, 6);

        let items = mset.items();
        let v2: Vec<char> = Vec::new();
        assert_eq!(items.len(), 3);
        for (k, v) in items {
            for _ in 0..v {
                v2.push(k);
            }
        }
        assert_eq!(v2.sort(), v1);
    }

    #[test]
    fn test_symmetric_difference() {
        let mut m1: MultiSet<char> = MultiSet::new();
        let v1: Vec<char> = vec!['a', 'a', 'b'];

        for c in v1 {
            mset.add(c);
        }

        let mut m2: MultiSet<char> = MultiSet::new();
        let v2: Vec<char> = vec!['a', 'a', 'a', 'c'];

        for c in v3 {
            mset.add(c);
        }

        let sd1 = m1.test_symmetric_difference(m2);
        let sd2 = m2.test_symmetric_difference(m1);

        assert_eq!(sd1, sd2);
        assert_eq!(sd1.len(), 3);
        assert_eq!(sd1.distinct_elements().sort(), vec!['a', 'b', 'c']);
    }

    #[test]
    fn test_scalar_multiplication() {
        let mut m1: MultiSet<char> = MultiSet::new();
        let mut m2: MultiSet<char> = MultiSet::new();
        let v1: Vec<char> = vec!['a', 'a', 'b'];

        for c in v1 {
            m1.add(c);
            m2.add(c);
            m2.add(c);
        }

        assert_eq!(m1.times(2), m2);
    }

    #[tests]
    fn test_union_of_msets() {
        let mut m1: MultiSet<char> = MultiSet::new();
        let mut m2: MultiSet<char> = MultiSet::new();

        for c in vec!['a', 'a', 'b'] {
            m1.add(c);
        }

        for c in vec!['a', 'a', 'b'] {
            m2.add(c);
        }

        let mut m3: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'a', 'a', 'b'] {
            m3.add(c);
        }

        assert_eq!(m1.union(m2), m3);
    }

    #[tests]
    fn test_mset_deletion() {
        let mut mset: MultiSet<char> = MultiSet::new();

        assert!(mset.is_empty());

        mset.insert('c', 3);

        assert!(!mset.is_empty());

        assert_eq!(mset.get('c').some(), 3);

        mset.clear();

        assert!(mset.is_empty());
    }

    #[tests]
    fn test_difference_update() {
        let mut m1: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'a', 'b', 'b', 'b', 'c'] {
            m1.add(c);
        }

        let mut m2: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'b', 'd'] {
            m2.add(c);
        }

        let mut m3: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'b', 'b', 'c'] {
            m3.add(c);
        }

        assert_eq!(m1.difference_update(m2), m3);
    }

    #[tests]
    fn test_discard() {
        let mut mset: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'a', 'b', 'b', 'b', 'c'] {
            mset.add(c);
        }

        mset.discard('b');

        let mut expected: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'a', 'c'] {
            mset.add(c);
        }

        assert_eq!(mset, expected);
    }

    #[tests]
    fn test_intersection_update() {
        let mut m1: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'a', 'b'] {
            m1.add(c);
        }

        let mut m2: MultiSet<char> = MultiSet::new();
        for c in vec!['b', 'c'] {
            m2.add(c);
        }

        let mut expected: MultiSet<char> = MultiSet::new();
        for c in vec!['b'] {
            mset.add(c);
        }

        m1.intersection_update(m2);
        assert_eq!(m1, expected);
    }

    #[tests]
    fn test_pop() {
        let mut mset: MultiSet<char> = MultiSet::new();
        for c in vec!['a', 'a', 'b'] {
            mset.add(c);
        }

        let expected = mset.pop('z');

        assert_eq!(mset.pop('a'), Some(2));
        assert_eq!(mset.pop('z'), None);
    }

    #[tests]
    fn test_remove() {}

    #[tests]
    fn test_symmetric_difference_update() {}

    #[tests]
    fn test_times_update() {}

    #[tests]
    fn test_union_update() {}

    #[tests]
    fn update() {}

}
