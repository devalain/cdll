use alloc::boxed::Box;
pub(crate) mod node;

use {
    crate::iter::{IntoIter, Iter, IterMut, RevIter},
    core::{marker::PhantomData, ptr::NonNull},
    node::Node,
};

pub struct CircularList<T> {
    pub(crate) head: Option<NonNull<Node<T>>>,
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
    pub fn new() -> Self {
        Self {
            head: None,
            _marker: PhantomData,
        }
    }

    pub fn clear(&mut self) {
        while self.pop_front().is_some() {}
    }
    pub fn len(&self) -> usize {
        self.iter().count()
    }
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    pub fn first(&self) -> Option<&T> {
        let head = self.head?;
        Some(unsafe { &(*head.as_ptr()).value })
    }
    pub fn last(&self) -> Option<&T> {
        let head = self.head?;
        Some(unsafe {
            let tail = (*head.as_ptr()).prev;
            &(*tail.as_ptr()).value
        })
    }

    pub fn push_back(&mut self, val: T) {
        if let Some(head) = self.head {
            unsafe {
                Node::insert_prev(head, val);
            }
        } else {
            self.head = Some(Node::new(val));
        }
    }
    pub fn push_front(&mut self, val: T) {
        self.push_back(val);
        self.rot(-1);
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let head = self.head?;
        let next = unsafe { Node::next_distinct(head) };
        let val = unsafe { Node::remove(head) };
        self.head = next;
        Some(val)
    }
    pub fn pop_back(&mut self) -> Option<T> {
        self.rot(-1);
        self.pop_front()
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter::from_list(self)
    }
    pub fn rev_iter(&self) -> RevIter<'_, T> {
        RevIter::from_list(self)
    }
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        IterMut::from_list(self)
    }

    pub fn split_half(&mut self) -> Option<Self> {
        let head = self.head?;
        let mid = unsafe { Node::half(self) }?;
        if head == mid {
            return None;
        }
        unsafe {
            Node::split(head, mid);
        }
        Some(Self {
            head: Some(mid),
            ..Default::default()
        })
    }

    pub fn rot(&mut self, n: isize) {
        if let Some(head) = self.head.as_mut() {
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

    pub fn extend_from_list(&mut self, mut other: Self) {
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
                other.head = None;
            },
        }
    }
}

impl<T: PartialEq> CircularList<T> {
    pub fn dedup(&mut self) {
        let Some(head) = self.head else {
            return;
        };
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
                } else {
                    prev_value = value;
                }
                current = next;
                value = &(*current.as_ptr()).value;
            }
        }
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
