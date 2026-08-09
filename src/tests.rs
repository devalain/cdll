extern crate std;
use super::*;

#[test]
fn list_constructor_empty() {
    let list: CircularList<i32> = CircularList::new();
    assert!(list.is_empty());
    assert_eq!(list, list![]);
}

#[test]
fn list_constructor_1() {
    let mut list: CircularList<i32> = CircularList::new();
    list.push_back(1);
    assert!(!list.is_empty());
    assert_eq!(list.len(), 1);
    assert_eq!(list, list![1]);
    assert_eq!(list.pop_front(), Some(1));
    assert_eq!(list.len(), 0);
    assert!(list.is_empty());
    assert_eq!(list.pop_front(), None);
}

#[test]
fn list_constructor_4() {
    let mut list = list![1, 2, 42, 666];
    let arr: alloc::vec::Vec<_> = list.iter().copied().collect();
    assert!(list.len() == 4);
    assert_eq!(arr.as_slice(), &[1, 2, 42, 666]);
    assert_eq!(list.pop_front(), Some(1));
    assert_eq!(list.pop_front(), Some(2));
    assert_eq!(list.pop_front(), Some(42));
    assert_eq!(list.pop_front(), Some(666));
    assert_eq!(list.pop_front(), None);
}

#[test]
fn list_clear() {
    let mut list = list![@each 1..=100];
    assert!(!list.is_empty());
    list.clear();
    assert!(list.is_empty());
}

#[test]
fn list_front_back() {
    let mut list = list!['A', 'B', 'C', 'D'];
    assert_eq!(list.front(), Some(&'A'));
    assert_eq!(list.back(), Some(&'D'));

    let first = list.front_mut().unwrap();
    *first = 'X';
    assert_eq!(list.front(), Some(&'X'));

    let last = list.back_mut().unwrap();
    *last = 'Y';
    assert_eq!(list.back(), Some(&'Y'));
}

#[test]
fn list_iter() {
    let list = list![@each 0..100];
    for (i, el) in list.iter().copied().enumerate() {
        assert_eq!(i, el as usize);
    }
}

#[test]
fn list_iter_rev() {
    let list = list![@each 0..100];
    for (i, el) in list.rev_iter().copied().enumerate() {
        assert_eq!(99 - i, el as usize);
    }
}

#[test]
fn list_iter_mut() {
    let mut list = list![@each 0..100];
    for el in list.iter_mut() {
        *el *= 2;
    }
    for (i, el) in list.iter().copied().enumerate() {
        assert_eq!(2 * i, el as usize);
    }
}

#[test]
fn list_into_iter() {
    let mut sum = 0;
    for x in list![@each 1..=100] {
        sum += x;
    }
    assert_eq!(sum, 5050);
}

#[test]
fn list_split_half() {
    let mut list = list![@each 1..=100];
    let other = list.split_half().unwrap();

    assert_eq!(list, (1..=50).collect::<CircularList<_>>());
    assert_eq!(list.len(), 50);
    assert_eq!(other, (51..=100).collect::<CircularList<_>>());
    assert_eq!(other.len(), 50);
}

#[test]
fn list_rotate() {
    let rot13: CircularList<(char, char)> = list![
        ('A', 'N'),
        ('B', 'O'),
        ('C', 'P'),
        ('D', 'Q'),
        ('E', 'R'),
        ('F', 'S'),
        ('G', 'T'),
        ('H', 'U'),
        ('I', 'V'),
        ('J', 'W'),
        ('K', 'X'),
        ('L', 'Y'),
        ('M', 'Z'),
        ('N', 'A'),
        ('O', 'B'),
        ('P', 'C'),
        ('Q', 'D'),
        ('R', 'E'),
        ('S', 'F'),
        ('T', 'G'),
        ('U', 'H'),
        ('V', 'I'),
        ('W', 'J'),
        ('X', 'K'),
        ('Y', 'L'),
        ('Z', 'M')
    ];

    let mut list = list![@each 'A'..='Z'];
    list.rotate(13);
    let map = list![@each 'A'..='Z']
        .into_iter()
        .zip(list.into_iter())
        .collect::<CircularList<_>>();

    assert_eq!(map, rot13);

    let mut list = list![@each 'A'..='Z'];
    list.rotate(-13);
    let map = list![@each 'A'..='Z']
        .into_iter()
        .zip(list.into_iter())
        .collect::<CircularList<_>>();

    assert_eq!(map, rot13);
}

#[test]
fn list_rotate_2() {
    let mut list = list![1, 2, 3, 4, 5];

    list.rotate(13);
    assert_eq!(list, list![4, 5, 1, 2, 3]);

    list.rotate(-13);
    assert_eq!(list, list![1, 2, 3, 4, 5]);
}

#[test]
fn list_append() {
    let mut a = list![1, 2, 3];
    let mut b = list![4, 5, 6];
    a.append(&mut b);
    assert_eq!(a, list![1, 2, 3, 4, 5, 6]);
    assert!(b.is_empty());
}

#[test]
fn list_contains() {
    let list = list![1, 2, 3, 4];
    assert!(list.contains(&3));
}

#[test]
fn list_dedup() {
    let mut list = list![1, 2, 2, 3, 2];
    list.dedup();
    assert_eq!(list, list![1, 2, 3, 2]);
}

#[test]
fn list_push_front_and_pop_back() {
    let mut list = list![1, 2, 3, 4, 5];

    list.push_front(0);
    assert_eq!(list, list![0, 1, 2, 3, 4, 5]);
    assert_eq!(list.pop_back(), Some(5));
}

#[test]
fn split_half_and_merge() {
    let list = list![3, 1, 8, 21, 5, 9, 12, 5, 2, 6, 6, 6, 13, 2, 17];
    let sorted = merge_sort(list);
    assert_eq!(
        sorted,
        list![1, 2, 2, 3, 5, 5, 6, 6, 6, 8, 9, 12, 13, 17, 21]
    )
}
fn merge_sort(mut list: CircularList<i32>) -> CircularList<i32> {
    if list.is_empty() || list.len() == 1 {
        return list;
    }

    let second = list.split_half().expect("List not empty");
    let mut list = merge_sort(list);
    let mut second = merge_sort(second);

    list.merge(&mut second);
    list
}
