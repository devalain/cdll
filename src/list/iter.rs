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

impl<'c, T> DoubleEndedIterator for Iter<'c, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let current = self.current.take()?;
        let next_back = Some(unsafe { (*current.as_ptr()).prev });
        if next_back != self.list.head {
            self.current = next_back;
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

impl<'c, T> DoubleEndedIterator for IterMut<'c, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let current = self.current.take()?;
        let next_back = Some(unsafe { (*current.as_ptr()).prev });
        if next_back != self.list.head {
            self.current = next_back;
        }
        Some(unsafe { &mut (*current.as_ptr()).value })
    }
}
