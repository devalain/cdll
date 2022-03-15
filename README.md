# Circular Linked List written in rust
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