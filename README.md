# Circular Doubly Linked List written in rust

[![crate][crate-image]][crate-link]
[![docs][docs-image]][docs-link]

Inspired from the linux kernel [list](https://github.com/torvalds/linux/blob/master/include/linux/list.h).

## Disclaimer
Do not use before `v0.5` as it was unsound ! This is a rewrite. The new developpement is test driven and 
`miri`-checked before commit.

## Basic usage
```rust
use cdll::{list, CircularList};

let mut list = list![1, 2, 3];
list.push_back(4);

assert_eq!(list, list![1, 2, 3, 4]);
assert_eq!(list.pop_front(), Some(1));

my_list.iter_mut().for_each(|x: &mut i32| *x -= 1);
assert_eq!(my_list.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);
```

[crate-image]: https://img.shields.io/crates/v/cdll.svg
[crate-link]: https://crates.io/crates/cdll

[docs-image]: https://docs.rs/cdll/badge.svg
[docs-link]: https://docs.rs/cdll