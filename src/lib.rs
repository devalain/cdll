//! Circular doubly linked list.
//! The implementation is inspired by the [linux implementation in `C`
//! ](https://github.com/torvalds/linux/blob/master/include/linux/list.h).
//!
//! # Basic usage
//! ```
//! use cll::CircularList;
//!
//! let mut my_list = CircularList::default();
//! for x in 1..=5 {
//!     my_list.add(x);
//! }
//!
//! assert_eq!(my_list.remove(), Some(1));
//! assert_eq!(my_list.pop(), Some(5));
//!
//! my_list.iter_mut().for_each(|x: &mut i32| *x -= 1);
//! assert_eq!(my_list.into_iter().collect::<Vec<i32>>(), &[1, 2, 3])
//! ```
//!
//! # Safety considerations
//! This crate uses `unsafe` code to dereference raw pointers. In order for it to be *sound*, one
//! has to preserve some invariants (i.e. pointers must be valid). To achieve this, the source code
//! is commented with careful justifications to *prove* correctness (at least it is a try).

mod head;

use {
    crate::head::{Iter, IterMut, ListHead},
    either::Either,
    std::{iter::FromIterator, ptr},
};

/// Create a list with provided elements.
/// # Exemple
/// ```
/// # use cll::list;
/// let primes = list![2, 3, 5, 7, 11];
/// println!("{:?}", primes);
/// ```
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

/// A circular doubly linked list.
pub struct CircularList<T> {
    // The `head` field is a pointer to a `ListHead<T>`. The code try to preserve the following
    // invariant (1): If the list is empty, it is null, otherwise it is a valid pointer that one
    // can safely dereference.
    head: *const ListHead<T>,

    // Obviously the number of elements in the list.
    // Invariant (2): It is updated each time an element is added to the list or removed from it.
    length: usize,
}
impl<T> CircularList<T> {
    /// Gets the size of the list.
    pub fn len(&self) -> usize {
        self.length
    }

    /// Returns `true` if the list contains no element.
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// Adds an element to the end of the list.
    ///
    /// # Exemple
    /// ```
    /// # use cll::list;
    /// # let mut my_list = list!["Follow the white rabbit"];
    /// my_list.add("Hello");
    /// assert_eq!(my_list.pop(), Some("Hello"))
    ///
    pub fn add(&mut self, val: T) {
        let new = Box::leak(ListHead::<T>::new(val));

        // If `self.head` is null (which means `self.length == 0` by (2)) then it is assigned to
        // a valid pointer to the `new` element, preserving (1).
        if self.head.is_null() {
            debug_assert_eq!(self.length, 0);
            self.head = new;
        } else {
            let head = self.head as *mut ListHead<T>;
            unsafe {
                // SAFETY: At this point, `head` must be valid since it was initialized to `new`
                // if it was null.
                (*head).add(new);
            }
        }

        // Preserving invariant (2)
        self.length += 1;
    }

    /// Removes the first element of the list and returns it if any.
    pub fn remove(&mut self) -> Option<T> {
        // If `self.head` is null (which means `self.length == 0` by (2))
        // then there is nothing to do.
        if self.head.is_null() {
            debug_assert_eq!(self.length, 0);
            None
        } else {
            let (new_head, old_val) = unsafe {
                // SAFETY: Since `head` is not null, it must be valid as we try to preserve (1).
                // Furthermore, it must be true that it has pointers to its next and previous
                // elements because of the invariant (3) (see the `head` module).
                ListHead::<T>::del(self.head as *mut _)
            };
            // If there is a next element, it is the new head, otherwise `self.head` is null.
            // Invariant (1) is preserved since de `ListHead::del` function returns either null
            // or a valid pointer by invariant (3).
            self.head = new_head;

            // Preserving invariant (2)
            self.length -= 1;

            debug_assert_eq!(self.head.is_null(), self.length == 0);
            Some(old_val)
        }
    }

    /// Removes the last element of the list and returns it if any.
    pub fn pop(&mut self) -> Option<T> {
        // If there is only 1 element in the list,
        // the first and the last are the same.
        if self.length == 1 {
            self.remove()
        } else if self.head.is_null() {
            // The list is empty so we check the invariant (2).
            debug_assert_eq!(self.length, 0);
            None
        } else {
            let (_, old_val) = unsafe {
                // SAFETY: Since `head` is not null, it must be valid because of (1).
                // Furthermore, it must be true that it has pointers to its next and previous
                // elements because of invariant (3).
                ListHead::<T>::del((*self.head).prev() as *mut _)
            };

            // Preserving invariant (2)
            self.length -= 1;
            Some(old_val)
        }
    }

    /// Exchanges the place of the element at position `i` and the element at position `j`.
    pub fn swap(&mut self, i: usize, j: usize) {
        // Do nothing if list is empty
        if self.is_empty() {
            return;
        }

        let i = i % self.length;
        let j = j % self.length;

        // Don't swap an element with itself.
        if i == j {
            return;
        }

        let from = i.min(j);
        let count = i.max(j) - from;
        let mut item1 = self.head as *mut ListHead<T>;
        for _ in 0..from {
            item1 = unsafe {
                // SAFETY: The invariant (3) asserts that the pointer to the next element
                // of a `ListHead` is always valid.
                (*item1).next()
            } as *mut _;
        }
        let mut item2 = item1;
        for _ in 0..count {
            item2 = unsafe {
                // SAFETY: The invariant (3) asserts that the pointer to the next element
                // of a `ListHead` is always valid.
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
                // SAFETY: `head` is not null, so it must be a valid pointer because of (1)
                // `other_head` is not null, so it must be a valid pointer for the same reason.
                // `head` is obviously not in the same list as `other_head` since `head` comes from
                // an exclusive reference of `Self` and `other_head` comes from an owned `Self`.
                ListHead::<T>::add_list(other_head, head);
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
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An owning iterator over the elements of a `CircularList`.
/// This `struct` is created by [`CircularList::into_iter()`].
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
        assert_eq!(a.len(), 7);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3, 4, 5, 6, 7]);

        let mut a = list![1, 2, 3];
        a.merge(list![]);
        assert_eq!(a.len(), 3);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);

        let mut a = list![];
        a.merge(list![1, 2, 3]);
        assert_eq!(a.len(), 3);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[1, 2, 3]);

        let mut a = list![];
        a.merge(list![]);
        assert_eq!(a.len(), 0);
        assert_eq!(a.into_iter().collect::<Vec<i32>>(), &[]);
    }
}
