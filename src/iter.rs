use {
    crate::{CircularList, list::node::Node},
    core::ptr::NonNull,
};

/// Immutable list iterator
///
/// This struct is created by the [`iter`] method on [`CircularList`].
///
/// [`iter`]: CircularList::iter
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
        let next = Some(unsafe { Node::next(current) });
        if next != self.list.head {
            self.current = next;
        }
        Some(unsafe { Node::value(current) })
    }
}

/// Immutable list iterator with the direction inverted.
///
/// This `struct` is created by the [`rev_iter`] method on [`CircularList`]. See its documentation for more.
///
/// [`rev_iter`]: CircularList::rev_iter
pub struct Rev<'c, T> {
    list: &'c CircularList<T>,
    current: Option<NonNull<Node<T>>>,
}
impl<'c, T> Rev<'c, T> {
    pub(super) fn from_list(list: &'c CircularList<T>) -> Self {
        Self {
            list,
            current: list.head.map(|h| unsafe { Node::prev(h) }),
        }
    }
}
impl<'c, T> Iterator for Rev<'c, T> {
    type Item = &'c T;
    fn next(&mut self) -> Option<Self::Item> {
        let current = self.current.take()?;
        if Some(current) != self.list.head {
            let prev = Some(unsafe { Node::prev(current) });
            self.current = prev;
        }
        Some(unsafe { Node::value(current) })
    }
}

/// Mutable list iterator
///
/// This struct is created by the [`iter_mut`] method on [`CircularList`].
///
/// [`iter_mut`]: CircularList::iter_mut
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
        let next = Some(unsafe { Node::next(current) });
        if next != self.list.head {
            self.current = next;
        }
        Some(unsafe { Node::value_mut(current) })
    }
}

/// Owned list iterator.
///
/// This `struct` is created by the [`into_iter`] method on [`CircularList`]. See its documentation for more.
///
/// [`into_iter`]: CircularList::into_iter
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
