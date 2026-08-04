mod node;
use {
    node::Node,
    std::{marker::PhantomData, ptr::NonNull},
};

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
        Some(val)
    }

    pub fn iter(&self) -> impl Iterator<Item = &T> + '_ {
        struct Iter<'c, T> {
            list: &'c CircularList<T>,
            current: Option<NonNull<Node<T>>>,
        }

        impl<'c, T> Iterator for Iter<'c, T> {
            type Item = &'c T;
            fn next(&mut self) -> Option<Self::Item> {
                let current = self.current.take()?;
                let next = Some(unsafe { (*current.as_ptr()).next });
                if next != self.list.head {
                    self.current = next;
                }
                Some(unsafe { &(*current.as_ptr()).value })
            }
        }

        Iter {
            list: self,
            current: self.head,
        }
    }
}

impl<T> Drop for CircularList<T> {
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}
