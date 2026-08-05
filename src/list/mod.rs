mod iter;
mod node;

use {
    core::{marker::PhantomData, ptr::NonNull},
    node::Node,
};

pub use iter::Iter;

pub struct CircularList<T> {
    head: Option<NonNull<Node<T>>>,
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: PartialEq> PartialEq for CircularList<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        let mut self_iter = self.iter();
        let mut other_iter = other.iter();
        while let Some(self_elem) = self_iter.next()
            && let Some(other_elem) = other_iter.next()
        {
            if self_elem != other_elem {
                return false;
            }
        }
        true
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
            len: 0,
            _marker: PhantomData,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn push_back(&mut self, val: T) {
        if let Some(head) = self.head {
            unsafe {
                Node::insert_prev(head, val);
            }
            self.len += 1;
        } else {
            self.head = Some(Node::new(val));
            self.len = 1;
        }
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let head = self.head?;
        let next = unsafe { Node::next_distinct(head) };
        let val = unsafe { Node::remove(head) };
        self.head = next;
        self.len -= 1;
        Some(val)
    }

    pub fn iter(&self) -> Iter<'_, T> {
        Iter::from_list(self)
    }
}

impl<T> Drop for CircularList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}
