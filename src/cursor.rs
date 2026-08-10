use {
    crate::{CircularList, list::node::Node},
    core::ptr::NonNull,
};

/// Cursor
///
/// This struct is created by the [`cursor`] method on [`CircularList`].
///
/// [`cursor`]: CircularList::cursor
pub struct Cursor<'c, T> {
    list: &'c CircularList<T>,
    current: NonNull<Node<T>>,
    index: usize,
}
impl<'c, T> Cursor<'c, T> {
    pub(super) fn from_list(list: &'c CircularList<T>) -> Option<Self> {
        list.head.map(|h| Self {
            list,
            current: h,
            index: 0,
        })
    }
}

impl<'c, T> Cursor<'c, T> {
    /// Returns the cursor position index within the `CircularList`.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Moves the cursor to the next element of the `CircularList`.
    ///
    /// If the cursor is pointing to the last element then this will move it to
    /// the first element of the `CircularList`.
    pub fn move_next(&mut self) {
        unsafe {
            self.current = (*self.current.as_ptr()).next;
        }
        self.index = (self.index + 1) % self.list.len();
    }
}
