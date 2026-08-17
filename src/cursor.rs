use {
    crate::{CircularList, list::node::Node},
    core::ptr::NonNull,
};

/// Cursor.
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
            self.current = Node::next(self.current);
        }
        self.index = (self.index + 1) % self.list.len();
    }

    /// Moves the cursor to the previous element of the `CircularList`.
    ///
    /// If the cursor is pointing to the first element then this will move it to
    /// the last element of the `CircularList`.
    pub fn move_prev(&mut self) {
        unsafe {
            self.current = Node::prev(self.current);
        }
        let len = self.list.len();
        self.index = (len + self.index - 1) % len;
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    pub fn current(&self) -> &'c T {
        unsafe { Node::value(self.current) }
    }

    /// Returns a reference to the next element.
    pub fn peek_next(&self) -> &'c T {
        unsafe {
            let next = Node::next(self.current);
            Node::value(next)
        }
    }

    /// Returns a reference to the previous element.
    pub fn peek_prev(&self) -> &'c T {
        unsafe {
            let prev = Node::prev(self.current);
            Node::value(prev)
        }
    }
}

/// Cursor with mutability on the list.
///
/// This struct is created by the [`cursor_mut`] method on [`CircularList`].
///
/// [`cursor_mut`]: CircularList::cursor_mut
pub struct CursorMut<'c, T> {
    list: &'c mut CircularList<T>,
    current: NonNull<Node<T>>,
    index: usize,
}
impl<'c, T> CursorMut<'c, T> {
    pub(super) fn from_list(list: &'c mut CircularList<T>) -> Option<Self> {
        list.head.map(|h| Self {
            list,
            current: h,
            index: 0,
        })
    }
}

impl<'c, T> CursorMut<'c, T> {
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
            self.current = Node::next(self.current);
        }
        self.index = (self.index + 1) % self.list.len();
    }

    /// Moves the cursor to the previous element of the `CircularList`.
    ///
    /// If the cursor is pointing to the first element then this will move it to
    /// the last element of the `CircularList`.
    pub fn move_prev(&mut self) {
        unsafe {
            self.current = Node::prev(self.current);
        }
        let len = self.list.len();
        self.index = (len + self.index - 1) % len;
    }

    /// Moves the node under the cursor to the next position.
    /// Does nothing if the list has less than 3 items.
    ///
    /// # Node
    /// This operation does not change which node is the head one.
    /// For instance,
    /// ```
    /// # use cdll::list;
    /// let mut list = list!['a', 'b', 'c', 'd'];
    /// list.cursor_mut().unwrap().move_node_next();
    /// assert_eq!(list, list!['a', 'c', 'd', 'b'])
    /// ```
    pub fn move_node_next(&mut self) {
        if self.list.len() < 3 {
            return;
        }

        let current = self.current;
        unsafe {
            let prev = Node::prev(current);
            let next = Node::next(current);
            let next_next = Node::next(next);

            Node::connect(current, next_next);
            Node::connect(next, current);
            Node::connect(prev, next);
        }
    }

    /// Moves the node under the cursor to the previous position.
    /// Does nothing if the list has less than 3 items.
    ///
    /// # Node
    /// This operation does not change which node is the head one.
    /// For instance,
    /// ```
    /// # use cdll::list;
    /// let mut list = list!['a', 'b', 'c', 'd', 'e'];
    /// list.cursor_mut().unwrap().move_node_prev();
    /// assert_eq!(list, list!['a', 'e', 'b', 'c', 'd'])
    /// ```
    pub fn move_node_prev(&mut self) {
        if self.list.len() < 3 {
            return;
        }

        let current = self.current;
        unsafe {
            let prev = Node::prev(current);
            let prev_prev = Node::prev(prev);
            let next = Node::next(current);

            Node::connect(current, prev);
            Node::connect(prev, next);
            Node::connect(prev_prev, current);
        }
    }

    /// Returns a reference to the element that the cursor is currently
    /// pointing to.
    pub fn current(&mut self) -> &'c mut T {
        unsafe { Node::value_mut(self.current) }
    }

    /// Returns a reference to the next element.
    pub fn peek_next(&self) -> &'c T {
        unsafe {
            let next = Node::next(self.current);
            Node::value(next)
        }
    }

    /// Returns a reference to the previous element.
    pub fn peek_prev(&self) -> &'c T {
        unsafe {
            let prev = Node::prev(self.current);
            Node::value(prev)
        }
    }
}
