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
    fn new() {
        let mset: MultiSet<char> = MultiSet::new();
    }

    #[test]
    fn add_and_retrieve_elements() {
        let mut mset: MultiSet<char> = MultiSet::new();
        mset.add('a');
        assert_eq!(mset.get('a'), 1);
        mset.add('a');
        assert_eq!(mset.get('a'), 2);

        mset.insert('b', 5);
        assert_eq!(mset.get('b'), 5);
    }

    #[test]
    fn combine_msets() {
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
    fn difference() {
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
    fn difference_update() {
        return true; // TODO mod in place
    }

    #[test]
    fn get_mset_values() {
        let mut m1: MultiSet<char> = MultiSet::new();
        m1.insert("dragons", 9);

        assert_eq!(m1.get("dragons"), Some(9));
        assert_eq!(m1.get("unicorns"), None);
    }

    #[test]
    fn intersection_of_msets() {
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
    fn msets_within_msets() {
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

}
