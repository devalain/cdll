//! Circular doubly linked list.
//! The implementation is inspired by the [linux implementation in `C`
//! ](https://github.com/torvalds/linux/blob/master/include/linux/list.h).
//!
//! # Basic usage
//! ```
//! use cll::list;
//! let mut my_list = list![1, 2, 3, 4, 5];
//!
//! assert_eq!(my_list.remove(), Some(1));
//! assert_eq!(my_list.pop(), Some(5));
//!
//! my_list.iter_mut().for_each(|x: &mut i32| *x -= 1);
//! assert_eq!(my_list.into_iter().collect::<Vec<i32>>(), &[1, 2, 3])
//! ```
mod head;

use {
    crate::head::{Iter, IterMut, ListHead},
    either::Either,
    std::{iter::FromIterator, ptr},
};

#[macro_export]
macro_rules! list {
    [$($elem:expr),* $(,)?] => {{
        #[allow(unused_mut)]
        let mut l = $crate::CircularList::default();
        $(
            l.add($elem);
        )*
        l
    }}
}

pub struct CircularList<T> {
    head: *const ListHead<T>,
    length: usize,
}
impl<T> CircularList<T> {
    pub fn len(&self) -> usize {
        self.length
    }
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }
    pub fn add(&mut self, val: T) {
        let new = Box::leak(ListHead::<T>::init(val));
        if self.head.is_null() {
            self.head = new;
        } else {
            let head = self.head as *mut ListHead<T>;
            unsafe {
                // SAFETY: At this point, `head` must be valid since it was initialized to `new`
                // if it was null.
                (*head).add(new);
            }
        }
        self.length += 1;
    }
    pub fn remove(&mut self) -> Option<T> {
        if self.head.is_null() {
            None
        } else {
            let (new_head, old_val) = unsafe {
                // SAFETY: Since `head` is not null, it must be valid... FIXME
                // Furthermore, it must be true that it has pointers to its next and previous
                // elements because... FIXME
                ListHead::<T>::del(self.head as *mut _)
            };
            self.head = new_head;
            self.length -= 1;
            Some(old_val)
        }
    }
    pub fn pop(&mut self) -> Option<T> {
        if self.length == 1 {
            self.remove()
        } else if self.head.is_null() {
            None
        } else {
            let (_, old_val) = unsafe {
                // SAFETY: Since `head` is not null, it must be valid... FIXME
                // Furthermore, it must be true that it has pointers to its next and previous
                // elements because... FIXME
                ListHead::<T>::del((*self.head).prev() as *mut _)
            };
            self.length -= 1;
            Some(old_val)
        }
    }
    pub fn swap(&mut self, i: usize, j: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }

        let i = i % self.length;
        let j = j % self.length;
        // Do nothing if i == j (mod `self.length`)
        if i == j {
            return;
        }

        let from = i.min(j);
        let count = i.max(j) - from;
        let mut item1 = self.head as *mut ListHead<T>;
        for _ in 0..from {
            item1 = unsafe {
                // SAFETY: FIXME
                (*item1).next()
            } as *mut _;
        }
        let mut item2 = item1;
        for _ in 0..count {
            item2 = unsafe {
                // SAFETY: FIXME
                (*item2).next()
            } as *mut _;
        }
        unsafe {
            // SAFETY: FIXME
            ListHead::<T>::swap(item1, item2);
        }
        if item1 as *const _ == self.head {
            self.head = item2 as *const _;
        } else if item2 as *const _ == self.head {
            self.head = item1 as *const _;
        }
    }
    pub fn merge(&mut self, mut other: Self) {
        if self.head.is_null() {
            self.head = other.head;
        } else if !other.head.is_null() {
            let other_head = other.head as *mut ListHead<T>;
            let head = self.head as *mut ListHead<T>;
            unsafe {
                // SAFETY: `head` is not null, so it must be a valid pointer because... FIXME
                // `other_head` is not null, so it must be a valid pointer for the same reason.
                // `last` is valid since... FIXME
                let last = (*head).prev() as *mut _;
                ListHead::<T>::add_list(other_head, last, head);
            }
        }
        self.length += other.length;

        // `other` must be in valid state when being dropped.
        other.head = ptr::null();
        other.length = 0;
    }
    pub fn left_rot(&mut self, count: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }
        let count = count % self.length;
        for _ in 0..count {
            self.head = unsafe {
                // SAFETY: FIXME
                (*self.head).next()
            };
        }
    }
    pub fn right_rot(&mut self, count: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }
        let count = count % self.length;
        for _ in 0..count {
            self.head = unsafe {
                // SAFETY: FIXME
                (*self.head).prev()
            };
        }
    }
    pub fn iter_forever(&self) -> impl Iterator<Item = &T> {
        if self.is_empty() {
            Either::Left(std::iter::empty())
        } else {
            Either::Right(Iter::new(self.head))
        }
    }
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.iter_forever().take(self.len())
    }
    pub fn iter_mut_forever(&mut self) -> impl Iterator<Item = &mut T> {
        if self.is_empty() {
            Either::Left(std::iter::empty())
        } else {
            Either::Right(IterMut::new(self.head as *mut _))
        }
    }
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        let len = self.len();
        self.iter_mut_forever().take(len)
    }
}
impl<T> Default for CircularList<T> {
    fn default() -> Self {
        Self {
            head: ptr::null(),
            length: 0,
        }
    }
}
impl<T: Clone> Clone for CircularList<T> {
    fn clone(&self) -> Self {
        let mut clone: Self = Default::default();
        for x in self.iter() {
            clone.add(x.clone());
        }
        clone
    }
}
impl<T> FromIterator<T> for CircularList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut new: Self = Default::default();
        for x in iter {
            new.add(x);
        }
        new
    }
}
impl<T> Drop for CircularList<T> {
    fn drop(&mut self) {
        while self.remove().is_some() {}
    }
}
impl<T: std::fmt::Debug> std::fmt::Debug for CircularList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list()
            .entries(self.iter_forever().take(self.len()))
            .finish()
    }
}

pub struct IntoIter<T>(CircularList<T>);
impl<T> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.0.remove()
    }
}
impl<T> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.0.pop()
    }
}
impl<T> IntoIterator for CircularList<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::<T>(self)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let l = CircularList::default();
        assert_eq!(l.iter().copied().collect::<Vec<i32>>(), &[]);
    }

    #[test]
    fn add() {
        let l = list![42, 43, 44, 45, 46];
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[42, 43, 44, 45, 46])
    }

    #[test]
    fn remove() {
        let mut l = list![42, 43, 44, 45, 46];
        assert_eq!(Some(42), l.remove());
        assert_eq!(Some(43), l.remove());
        assert_eq!(Some(44), l.remove());
        assert_eq!(Some(45), l.remove());
        assert_eq!(Some(46), l.remove());
    }

    #[test]
    fn mutating() {
        let mut l = list![42, 43, 44, 45, 46];
        for x in l.iter_mut() {
            *x += 1;
        }
        assert_eq!(
            l.iter().copied().collect::<Vec<i32>>(),
            &[43, 44, 45, 46, 47]
        );
    }

    #[test]
    fn swap() {
        for (i, j, expected) in [
            (1, 3, &[42, 45, 44, 43, 46]),
            (0, 1, &[43, 42, 44, 45, 46]),
            (1, 2, &[42, 44, 43, 45, 46]),
            (3, 4, &[42, 43, 44, 46, 45]),
            (2, 2, &[42, 43, 44, 45, 46]),
            (0, 4, &[46, 43, 44, 45, 42]),
        ] {
            let mut l = list![42, 43, 44, 45, 46];
            l.swap(i, j);
            assert_eq!(l.into_iter().collect::<Vec<i32>>(), expected);
        }

        let mut l = list![42, 43];
        l.swap(0, 1);
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[43, 42]);
    }

    #[test]
    fn left_rotate() {
        let mut l = list![42, 43, 44, 45, 46];
        l.left_rot(3);
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[45, 46, 42, 43, 44]);
    }

    #[test]
    fn right_rotate() {
        let mut l = list![42, 43, 44, 45, 46];
        l.right_rot(3);
        assert_eq!(l.into_iter().collect::<Vec<i32>>(), &[44, 45, 46, 42, 43]);
    }

    #[test]
    fn into_iter_double_ended_iterator() {
        let numbers = list![1, 2, 3, 4, 5, 6];

        let mut iter = numbers.into_iter();

        assert_eq!(Some(1), iter.next());
        assert_eq!(Some(6), iter.next_back());
        assert_eq!(Some(5), iter.next_back());
        assert_eq!(Some(2), iter.next());
        assert_eq!(Some(3), iter.next());
        assert_eq!(Some(4), iter.next());
        assert_eq!(None, iter.next());
        assert_eq!(None, iter.next_back());
    }

    #[test]
    fn iter_forever() {
        let numbers = list![1, 2, 3, 4, 5, 6];
        let double_sum = numbers
            .iter_forever()
            .take(2 * numbers.len())
            .copied()
            .sum();
        assert_eq!(42, double_sum);
    }

    #[test]
    fn from_iterator() {
        let mut numbers: CircularList<_> = vec![4, 5, 6, 7].into_iter().collect();
        assert_eq!(Some(7), numbers.pop());
        assert_eq!(Some(6), numbers.pop());
        assert_eq!(Some(5), numbers.pop());
        assert_eq!(Some(4), numbers.pop());
        assert_eq!(None, numbers.pop());
    }

    #[test]
    fn into_iter_rev() {
        let numbers = list![1, 2, 3];
        let mut iter = numbers.into_iter().rev();
        assert_eq!(Some(3), iter.next());
        assert_eq!(Some(2), iter.next());
        assert_eq!(Some(1), iter.next());
        assert_eq!(None, iter.next());
    }

    #[test]
    fn merge() {
        let mut a = list![1, 2, 3];
        let b = list![4, 5, 6, 7];
        a.merge(b);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3, 4, 5, 6, 7]);

        let mut a = list![1, 2, 3];
        a.merge(list![]);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);

        let mut a = list![];
        a.merge(list![1, 2, 3]);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);

        let mut a = list![];
        a.merge(list![]);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[]);
    }
}
