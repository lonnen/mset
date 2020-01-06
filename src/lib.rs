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
        return true
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let mset: MultiSet<i32> = MultiSet::new();
    }
}
