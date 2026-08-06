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
    let arr: Vec<_> = list.iter().copied().collect();
    assert!(list.len() == 4);
    assert_eq!(arr.as_slice(), &[1, 2, 42, 666]);
    assert_eq!(list.pop_front(), Some(1));
    assert_eq!(list.pop_front(), Some(2));
    assert_eq!(list.pop_front(), Some(42));
    assert_eq!(list.pop_front(), Some(666));
    assert_eq!(list.pop_front(), None);
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
fn list_split_at() {
    let mut list = list![@each 1..=100];
    let other = list.split_half().unwrap();

    assert_eq!(list, (1..=50).collect::<CircularList<_>>());
    assert_eq!(list.len(), 50);
    assert_eq!(other, (51..=100).collect::<CircularList<_>>());
    assert_eq!(other.len(), 50);
}
