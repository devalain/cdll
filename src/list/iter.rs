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
