use mset::MultiSet;
use std::collections::hash_map::RandomState;

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
    for (e, m) in mset.iter() {
        println!("{}, {}", e, m);
    }
    mset.remove(&'a');
    mset.remove(&'a');

    println!(" .  . . ");

    for (e, m) in mset.iter() {
        println!("{}, {}", e, m);
    }

    println!(" .  . . ");
    mset.remove_times(&'b', 2);
    mset.shrink_to_fit();
    for (e, m) in mset.iter() {
        println!("{}, {}", e, m);
    }
    assert_eq!(mset.capacity(), 0);

    let mut m = MSC::new();
    m.reserve(0);
    assert_eq!(m.capacity(), 0);
}

#[test]
fn test_insert_and_retrieve_elements() {
    let mut mset = MultiSet::new();
    mset.insert('a');
    assert_eq!(mset.get(&'a'), Some(&1));
    mset.insert('a');
    assert_eq!(mset.get(&'a'), Some(&2));

    mset.insert_times('b', 5);
    assert_eq!(mset.get(&'b'), Some(&5));
}

#[test]
fn test_iterator_over_elements() {
    let mut mset = MultiSet::with_capacity(4);
    mset.insert_times('a', 10);
    mset.insert_times('b', 5);
    mset.insert_times('c', 1);

    let mut observed: usize = 0;
    let mut observed_len: usize = 0;

    for (_e, m) in &mset {
        observed_len += 1;
        observed += m;
    }

    assert_eq!(mset.elements().len(), observed_len);
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
    let mut m1 = MultiSet::new();
    m1.insert_times('d', 9);

    assert_eq!(m1.get(&'d'), Some(&9));
    assert_eq!(m1.get(&'u'), None);
}

#[test]
fn test_mset_clear() {
    let mut mset = MultiSet::new();

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
    let expected = [1, 3, 3, 5, 6, 11, 11, 11];
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
    let expected = [3, 11, 11];
    for x in p.intersection(&q) {
        assert!(expected.contains(x));
        i += x;
    }
    assert_eq!(i, expected.iter().sum());
}

#[test]
fn test_difference() {
    let p: MultiSet<_> = [3, 5, 5, 11, 11].iter().cloned().collect();
    let q: MultiSet<_> = [1, 3, 3, 6, 11].iter().cloned().collect();

    let mut i = 0;
    let expected = [5, 5, 11];
    for e in p.difference(&q) {
        assert!(expected.contains(e));
        i += e;
    }

    assert_eq!(i, expected.iter().sum());

    i = 0;
    let expected = [1, 3, 6];
    for e in q.difference(&p) {
        assert!(expected.contains(e));
        i += e;
    }

    assert_eq!(i, expected.iter().sum());
}

#[test]
fn test_symmetric_difference() {
    let p: MultiSet<_> = [1, 3, 3, 3, 3, 5, 9, 11].iter().collect();
    let q: MultiSet<_> = [2, 3, 3, 5, 9, 14, 22, 22].iter().collect();

    let mut i = 0;
    let expected = [1, 3, 3, 11, 2, 14, 22, 22];
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
    let mset: MultiSet<_> = [777, 7, 7, 7].iter().cloned().collect();
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

    assert_eq!(a.elements().len(), 4);
    assert_eq!(a.len(), 5);
    assert!(a.contains(&1));
    assert!(a.contains(&2));
    assert!(a.contains(&3));
    assert!(a.contains(&4));

    assert_eq!(a.get(&1), Some(&2));
    assert_eq!(a.get(&2), Some(&1));
    assert_eq!(a.get(&5), None);

    let b: MultiSet<_> = [1, 2, 5].iter().cloned().collect();

    a.extend(&b);

    assert_eq!(a.elements().len(), 5);
    assert_eq!(a.len(), 8);

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
    let mut mset: MultiSet<_> = [1, 2, 3, 4, 5, 4, 3, 2, 1].iter().cloned().collect();
    mset.retain(|&k, _v| k < 3);

    assert_eq!(mset.elements().len(), 2);
    assert_eq!(mset.len(), 4);

    assert_eq!(mset.get(&1), Some(&2usize));
    assert_eq!(mset.get(&2), Some(&2usize));

    let mut mset: MultiSet<_> = [1, 2, 3, 4, 5, 4, 3, 2, 1].iter().cloned().collect();
    mset.retain(|&_k, v| {
        v == 1
    });

    assert_eq!(mset.elements().len(), 1);
    assert_eq!(mset.get(&5), Some(&1usize));
}
