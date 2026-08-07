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
fn list_first_last() {
    let list = list!['A', 'B', 'C', 'D'];
    assert_eq!(list.first(), Some(&'A'));
    assert_eq!(list.last(), Some(&'D'));
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
fn list_rot() {
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
    list.rot(13);
    let map = list![@each 'A'..='Z']
        .into_iter()
        .zip(list.into_iter())
        .collect::<CircularList<_>>();

    assert_eq!(map, rot13);

    let mut list = list![@each 'A'..='Z'];
    list.rot(-13);
    let map = list![@each 'A'..='Z']
        .into_iter()
        .zip(list.into_iter())
        .collect::<CircularList<_>>();

    assert_eq!(map, rot13);
}

#[test]
fn list_extend() {
    let mut a = list![1, 2, 3];
    let b = list![4, 5, 6];
    a.extend_from_list(b);
    assert_eq!(a, list![1, 2, 3, 4, 5, 6]);
}

#[test]
fn list_dedup() {
    let mut list = list![1, 2, 2, 3, 2];
    list.dedup();
    assert_eq!(list, list![1, 2, 3, 2]);
}
