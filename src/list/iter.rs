use {
    crate::{CircularList, list::Node},
    core::ptr::NonNull,
};

pub struct Iter<'c, T> {
    list: &'c CircularList<T>,
    current: Option<NonNull<Node<T>>>,
}
impl<'c, T> Iter<'c, T> {
    pub(super) fn from_list(list: &'c CircularList<T>) -> Self {
        Self {
            list,
            current: list.head,
        }
    }
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

pub struct RevIter<'c, T> {
    list: &'c CircularList<T>,
    current: Option<NonNull<Node<T>>>,
}
impl<'c, T> RevIter<'c, T> {
    pub(super) fn from_list(list: &'c CircularList<T>) -> Self {
        Self {
            list,
            current: list.head.map(|h| unsafe { (*h.as_ptr()).prev }),
        }
    }
}
impl<'c, T> Iterator for RevIter<'c, T> {
    type Item = &'c T;
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current.take()?;
        if Some(current) != self.list.head {
            let prev = Some(unsafe { (*current.as_ptr()).prev });
            self.current = prev;
        }
        Some(unsafe { &(*current.as_ptr()).value })
    }
}

pub struct IterMut<'c, T> {
    list: &'c mut CircularList<T>,
    current: Option<NonNull<Node<T>>>,
}
impl<'c, T> IterMut<'c, T> {
    pub(super) fn from_list(list: &'c mut CircularList<T>) -> Self {
        let current = list.head;
        Self { list, current }
    }
}
impl<'c, T> Iterator for IterMut<'c, T> {
    type Item = &'c mut T;
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current.take()?;
        let next = Some(unsafe { (*current.as_ptr()).next });
        if next != self.list.head {
            self.current = next;
        }
        Some(unsafe { &mut (*current.as_ptr()).value })
    }
}

pub struct IntoIter<T> {
    list: CircularList<T>,
}
impl<T> IntoIter<T> {
    pub(super) fn from_list(list: CircularList<T>) -> Self {
        Self { list }
    }
}
impl<T> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<Self::Item> {
        self.list.pop_front()
    }
}
