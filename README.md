# Circular Linked List written in rust

[![crate][crate-image]][crate-link]
[![docs][docs-image]][docs-link]

Inspired from the linux kernel [list](https://github.com/torvalds/linux/blob/master/include/linux/list.h).

## Basic usage
```rust
use cll::CircularList;

let mut my_list = CircularList::default();
for x in 1..=5 {
    my_list.add(x);
}

assert_eq!(my_list.remove(), Some(1));
assert_eq!(my_list.pop(), Some(5));

my_list.iter_mut().for_each(|x: &mut i32| *x -= 1);
assert_eq!(my_list.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);
```

## Example of sorting using `double_cursor`
```rust
use cll::list;

let mut list = list![3, 1, 8, 21, 5, 9, 12, 5, 2, 6, 6, 6, 13, 2, 17];
let len = list.len();
let mut dc = list
    .double_cursor()
    .expect("A cursor should always be available on a non empty list");

let mut min = *dc.value_a();
for i in 1..len {
    dc.set_b_to_a();
    dc.push_a();
    for _ in i..len {
        dc.move_next_a();
        let val = *dc.value_a();
        if val < min {
            min = val;
            dc.set_b_to_a();
        }
    }
    dc.pop_a();
    dc.insert_b_before_a();
    if dc.a_is_b() {
        dc.move_next_a();
    }
    min = *dc.value_a();
}
assert_eq!(
    list.into_iter().collect::<Vec<i32>>(),
    &[1, 2, 2, 3, 5, 5, 6, 6, 6, 8, 9, 12, 13, 17, 21]
);
```

[crate-image]: https://img.shields.io/crates/v/cdll.svg
[crate-link]: https://crates.io/crates/cdll

[docs-image]: https://docs.rs/cdll/badge.svg
[docs-link]: https://docs.rs/cdll