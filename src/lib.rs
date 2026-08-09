#![no_std]
//! Circular doubly linked list.
//!
//! # Basic usage
//! ```
//! # use cdll::{list, CircularList};
//! let mut list = list![1, 2, 3];
//!
//! list.push_back(4);
//! assert_eq!(list, list![1, 2, 3, 4]);
//! assert_eq!(list.pop_front(), Some(1));
//! ```

extern crate alloc;

mod iter;
mod list;

#[macro_use]
mod macros;

#[cfg(test)]
mod tests;

pub use {
    iter::{IntoIter, Iter, IterMut, Rev},
    list::CircularList,
};
