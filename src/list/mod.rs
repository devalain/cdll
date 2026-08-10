use alloc::boxed::Box;
pub(crate) mod node;

use crate::cursor::Cursor;

use {
    crate::iter::{IntoIter, Iter, IterMut, Rev},
    core::{marker::PhantomData, ptr::NonNull},
    node::Node,
};

/// A circular doubly linked list with owned nodes. It is similar to the
/// standard library [`LinkedList`] (the API is almost the same) exept it is circular
/// (i.e. the last element is linked to the first).
///
/// [`LinkedList`]: https://doc.rust-lang.org/std/collections/struct.LinkedList.html
pub struct CircularList<T> {
    pub(crate) head: Option<NonNull<Node<T>>>,
    len: usize,
    _marker: PhantomData<Box<Node<T>>>,
}

impl<T> Default for CircularList<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Clone> Clone for CircularList<T> {
    fn clone(&self) -> Self {
        let mut clone: Self = Default::default();
        for x in self.iter() {
            clone.push_back(x.clone());
        }
        clone
    }
}
impl<T: core::fmt::Debug> core::fmt::Debug for CircularList<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: PartialEq> PartialEq for CircularList<T> {
    fn eq(&self, other: &Self) -> bool {
        let mut self_iter = self.iter();
        let mut other_iter = other.iter();

        loop {
            match (self_iter.next(), other_iter.next()) {
                (Some(self_elem), Some(other_elem)) if self_elem == other_elem => {}
                (None, None) => break true,
                _ => break false,
            }
        }
    }
}
impl<T: Eq> Eq for CircularList<T> {}

impl<T> FromIterator<T> for CircularList<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut new: Self = Default::default();
        for x in iter {
            new.push_back(x);
        }
        new
    }
}

impl<T> CircularList<T> {
    /// Create an empty `CircularList`.
    ///
    /// # Examples
    /// ```
    /// use cdll::CircularList;
    ///
    /// let list: CircularList<i32> = CircularList::new();
    /// ```
    pub fn new() -> Self {
        Self {
            head: None,
            len: 0,
            _marker: PhantomData,
        }
    }

    /// Removes all elements from the `CircularList`.
    ///
    /// This operation should compute in *O*(*n*) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    ///
    /// cl.push_front(2);
    /// cl.push_front(1);
    /// assert_eq!(cl.len(), 2);
    /// assert_eq!(cl.front(), Some(&1));
    ///
    /// cl.clear();
    /// assert_eq!(cl.len(), 0);
    /// assert_eq!(cl.front(), None);
    /// ```
    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }

    /// Returns the length of the `CircularList`.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    ///
    /// cl.push_front(2);
    /// assert_eq!(cl.len(), 1);
    ///
    /// cl.push_front(1);
    /// assert_eq!(cl.len(), 2);
    ///
    /// cl.push_back(3);
    /// assert_eq!(cl.len(), 3);
    /// ```
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns `true` if the `CircularList` is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    /// assert!(cl.is_empty());
    ///
    /// cl.push_front("foo");
    /// assert!(!cl.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Provides a reference to the front element, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    /// assert_eq!(cl.front(), None);
    ///
    /// cl.push_front(1);
    /// assert_eq!(cl.front(), Some(&1));
    /// ```
    pub fn front(&self) -> Option<&T> {
        let head = self.head?;
        Some(unsafe { &(*head.as_ptr()).value })
    }

    /// Provides a mutable reference to the front element, or `None` if the list
    /// is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    /// assert_eq!(cl.front(), None);
    ///
    /// cl.push_front(1);
    /// assert_eq!(cl.front(), Some(&1));
    ///
    /// match cl.front_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(cl.front(), Some(&5));
    /// ```
    pub fn front_mut(&mut self) -> Option<&mut T> {
        let head = self.head?;
        Some(unsafe { &mut (*head.as_ptr()).value })
    }

    /// Provides a reference to the back element, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    /// assert_eq!(cl.back(), None);
    ///
    /// cl.push_back(1);
    /// assert_eq!(cl.back(), Some(&1));
    /// ```
    pub fn back(&self) -> Option<&T> {
        let head = self.head?;
        Some(unsafe {
            let tail = (*head.as_ptr()).prev;
            &(*tail.as_ptr()).value
        })
    }

    /// Provides a mutable reference to the back element, or `None` if the list
    /// is empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    /// assert_eq!(cl.back(), None);
    ///
    /// cl.push_back(1);
    /// assert_eq!(cl.back(), Some(&1));
    ///
    /// match cl.back_mut() {
    ///     None => {},
    ///     Some(x) => *x = 5,
    /// }
    /// assert_eq!(cl.back(), Some(&5));
    /// ```
    pub fn back_mut(&mut self) -> Option<&mut T> {
        let head = self.head?;
        Some(unsafe {
            let tail = (*head.as_ptr()).prev;
            &mut (*tail.as_ptr()).value
        })
    }

    /// Adds an element to the back of the list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut c = CircularList::new();
    /// c.push_back(1);
    /// c.push_back(3);
    /// assert_eq!(3, *c.back().unwrap());
    /// ```
    pub fn push_back(&mut self, val: T) {
        if let Some(head) = self.head {
            unsafe {
                Node::insert_prev(head, val);
            }
        } else {
            self.head = Some(Node::new(val));
        }
        self.len += 1;
    }

    /// Adds an element to the front of the list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut cl = CircularList::new();
    ///
    /// cl.push_front(2);
    /// assert_eq!(cl.front().unwrap(), &2);
    ///
    /// cl.push_front(1);
    /// assert_eq!(cl.front().unwrap(), &1);
    /// ```
    pub fn push_front(&mut self, val: T) {
        self.push_back(val);
        self.rotate(-1);
    }

    /// Removes the first element and returns it, or `None` if the list is
    /// empty.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut c = CircularList::new();
    /// assert_eq!(c.pop_front(), None);
    ///
    /// c.push_front(1);
    /// c.push_front(3);
    /// assert_eq!(c.pop_front(), Some(3));
    /// assert_eq!(c.pop_front(), Some(1));
    /// assert_eq!(c.pop_front(), None);
    /// ```
    pub fn pop_front(&mut self) -> Option<T> {
        let head = self.head?;
        let next = unsafe { Node::next_distinct(head) };
        let val = unsafe { Node::remove(head) };
        self.head = next;
        self.len -= 1;
        Some(val)
    }

    /// Adds an element to the back of the list.
    ///
    /// This operation should compute in *O*(1) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut c = CircularList::new();
    /// c.push_back(1);
    /// c.push_back(3);
    /// assert_eq!(3, *c.back().unwrap());
    /// ```
    pub fn pop_back(&mut self) -> Option<T> {
        self.rotate(-1);
        self.pop_front()
    }

    /// Provides a forward iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut list: CircularList<u32> = CircularList::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::from_list(self)
    }

    /// Provides a forward iterator with mutable references.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut list: CircularList<u32> = CircularList::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// for element in list.iter_mut() {
    ///     *element += 10;
    /// }
    ///
    /// let mut iter = list.iter();
    /// assert_eq!(iter.next(), Some(&10));
    /// assert_eq!(iter.next(), Some(&11));
    /// assert_eq!(iter.next(), Some(&12));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::from_list(self)
    }

    /// Provides a backward iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut list: CircularList<u32> = CircularList::new();
    ///
    /// list.push_back(0);
    /// list.push_back(1);
    /// list.push_back(2);
    ///
    /// let mut iter = list.rev_iter();
    /// assert_eq!(iter.next(), Some(&2));
    /// assert_eq!(iter.next(), Some(&1));
    /// assert_eq!(iter.next(), Some(&0));
    /// assert_eq!(iter.next(), None);
    /// ```
    pub fn rev_iter(&self) -> Rev<'_, T> {
        Rev::from_list(self)
    }

    /// Provides a cursor at the front element.
    ///
    /// If the list is empty, returns `None`.
    pub fn cursor(&self) -> Option<Cursor<'_, T>> {
        Cursor::from_list(self)
    }

    /// Extracts one half of the list and returns it as a new list.
    ///
    /// If the list is empty, this returns `None`.
    ///
    /// The extracted list is the greater half if the length is odd.
    ///
    /// This operation is *O*(*n*).
    ///
    /// # Examples
    /// ```
    /// use cdll::list;
    ///
    /// let mut list = list![1, 2, 3];
    /// let half = list.split_half();
    /// assert_eq!(half, Some(list![2, 3]));
    /// ```
    pub fn split_half(&mut self) -> Option<Self> {
        let head = self.head?;
        let len = self.len;
        let (mid, idx) = unsafe { Node::half(self) }?;
        if head == mid {
            return Some(core::mem::take(self));
        }
        unsafe {
            Node::split(head, mid);
        }
        self.len = idx;
        Some(Self {
            head: Some(mid),
            len: len - idx,
            ..Default::default()
        })
    }

    /// If mid is positive, rotates the list in-place such that the first `mid`
    /// elements of the list move to the end while the last `self.len() - mid`
    /// elements move to the front.
    ///
    /// If mid is negative, rotates the list in-place such that the first
    /// `self.len() + mid` elements of the list move to the end while the last
    /// `-mid` elements move to the front.
    ///
    /// Only the Euclid remainder of `mid` modulo `self.len()` is used.
    ///
    /// # Complexity
    ///
    /// Takes linear (in `mid % self.len()`) time.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::list;
    /// let mut a = list!['a', 'b', 'c', 'd', 'e', 'f'];
    /// a.rotate(2);
    /// assert_eq!(a, list!['c', 'd', 'e', 'f', 'a', 'b']);
    /// ```
    ///
    /// ```
    /// use cdll::list;
    /// let mut a = list!['a', 'b', 'c', 'd', 'e', 'f'];
    /// a.rotate(-2);
    /// assert_eq!(a, list!['e', 'f', 'a', 'b', 'c', 'd']);
    /// ```
    pub fn rotate(&mut self, mid: isize) {
        let len = self.len() as isize;
        if let Some(head) = self.head.as_mut() {
            let n = mid.rem_euclid(len);
            if n < 0 {
                for _ in 0..-n {
                    unsafe {
                        *head = (*head.as_ptr()).prev;
                    }
                }
            } else {
                for _ in 0..n {
                    unsafe {
                        *head = (*head.as_ptr()).next;
                    }
                }
            }
        }
    }

    /// Moves all elements from `other` to the end of the list.
    ///
    /// This reuses all the nodes from `other` and moves them into `self`. After
    /// this operation, `other` becomes empty.
    ///
    /// This operation should compute in *O*(1) time and *O*(1) memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::CircularList;
    ///
    /// let mut list1 = CircularList::new();
    /// list1.push_back('a');
    ///
    /// let mut list2 = CircularList::new();
    /// list2.push_back('b');
    /// list2.push_back('c');
    ///
    /// list1.append(&mut list2);
    ///
    /// let mut iter = list1.iter();
    /// assert_eq!(iter.next(), Some(&'a'));
    /// assert_eq!(iter.next(), Some(&'b'));
    /// assert_eq!(iter.next(), Some(&'c'));
    /// assert!(iter.next().is_none());
    ///
    /// assert!(list2.is_empty());
    /// ```
    pub fn append(&mut self, other: &mut Self) {
        match (self.head, other.head) {
            (None, None) => {}
            (Some(head), None) | (None, Some(head)) => {
                self.head = Some(head);
            }
            (Some(head_a), Some(head_b)) => unsafe {
                let tail_a = (*head_a.as_ptr()).prev;
                let tail_b = (*head_b.as_ptr()).prev;
                Node::connect(tail_a, head_b);
                Node::connect(tail_b, head_a);
            },
        }
        self.len += other.len;
        other.head = None;
        other.len = 0;
    }
}

impl<T: PartialEq> CircularList<T> {
    /// Returns `true` if the list contains an element with the given value.
    ///
    /// This operation is *O*(*n*).
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::list;
    ///
    /// let l = list![10, 40, 30];
    /// assert!(l.contains(&30));
    /// assert!(!l.contains(&50));
    /// ```
    pub fn contains(&self, elem: &T) -> bool {
        self.iter().any(|x| x == elem)
    }

    /// Removes consecutive repeated elements in the list according to the
    /// [`PartialEq`] trait implementation.
    ///
    /// If the list is sorted, this removes all duplicates.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::list;
    ///
    /// let mut list = list![1, 2, 2, 3, 2];
    ///
    /// list.dedup();
    ///
    /// assert_eq!(list, list![1, 2, 3, 2]);
    /// ```
    pub fn dedup(&mut self) {
        let Some(head) = self.head else {
            return;
        };
        let mut len = self.len;
        unsafe {
            let mut prev_value = &(*head.as_ptr()).value;
            let mut current = (*head.as_ptr()).next;
            let mut value = &(*current.as_ptr()).value;

            loop {
                if current == head {
                    break;
                }
                let next = (*current.as_ptr()).next;
                if value == prev_value {
                    let _ = Node::remove(current);
                    len -= 1;
                } else {
                    prev_value = value;
                }
                current = next;
                value = &(*current.as_ptr()).value;
            }
        }
        self.len = len;
    }
}

impl<T: PartialOrd> CircularList<T> {
    /// Moves all elements from `other` to the list keeping it ordered if it is the case.
    ///
    /// This reuses all the nodes from `other` and moves them into `self`. After
    /// this operation, `other` becomes empty.
    ///
    /// This operation should compute in *O*(*n*) time and *O*(1) memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use cdll::{CircularList, list};
    ///
    /// let mut list1 = CircularList::new();
    /// list1.push_back('a');
    /// list1.push_back('c');
    ///
    /// let mut list2 = CircularList::new();
    /// list2.push_back('b');
    /// list2.push_back('d');
    ///
    /// list1.merge(&mut list2);
    ///
    /// assert_eq!(list1, list!['a', 'b', 'c', 'd']);
    /// assert!(list2.is_empty());
    /// ```
    pub fn merge(&mut self, other: &mut Self) {
        match (self.head, other.head) {
            (None, None) => {}
            (Some(head), None) | (None, Some(head)) => {
                self.head = Some(head);
            }
            (Some(head_a), Some(head_b)) => unsafe {
                self.head = Some(Node::merge(head_a, head_b));
            },
        }
        self.len += other.len;
        other.len = 0;
        other.head = None;
    }
}

impl<T> Extend<T> for CircularList<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for val in iter {
            self.push_back(val);
        }
    }
}

impl<T> IntoIterator for CircularList<T> {
    type IntoIter = IntoIter<T>;
    type Item = T;
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::from_list(self)
    }
}

impl<T> Drop for CircularList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}
