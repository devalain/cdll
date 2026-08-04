use super::*;

#[test]
fn list_works() {
    let n: CircularList<i32> = CircularList::new();
    let arr: Vec<i32> = n.iter().copied().collect();
    assert!(n.is_empty());
    assert_eq!(arr.as_slice(), &[]);

    let mut n: CircularList<i32> = CircularList::new();
    n.push_back(1);
    let arr: Vec<_> = n.iter().copied().collect();
    assert!(n.len() == 1);
    assert_eq!(arr.as_slice(), &[1]);
    let val = n.pop_front();
    assert_eq!(val, Some(1));
    assert_eq!(n.pop_front(), None);

    let mut n = list![1, 2, 42, 666];
    let arr: Vec<_> = n.iter().copied().collect();
    assert!(n.len() == 4);
    assert_eq!(arr.as_slice(), &[1, 2, 42, 666]);
    assert_eq!(n.pop_front(), Some(1));
    assert_eq!(n.pop_front(), Some(2));
    assert_eq!(n.pop_front(), Some(42));
    assert_eq!(n.pop_front(), Some(666));
    assert_eq!(n.pop_front(), None);
}
