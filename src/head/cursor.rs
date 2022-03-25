use {super::ListHead, std::marker::PhantomData};

/// A `Cursor` is like an iterator, except that it can freely seek back-and-forth.
/// This `struct` is constructed by the [`CircularList::cursor`](crate::CircularList::cursor)
/// function.
#[derive(Clone, Copy)]
pub struct Cursor<'life, T> {
    // Invariant (4): `current` is a valid pointer.
    current: *const ListHead<T>,
    _marker: PhantomData<&'life T>,
}

impl<'life, T> Cursor<'life, T> {
    /// Builds a `Cursor` from a (valid) pointer to a `ListHead<T>`.
    /// # Safety
    /// The caller has to make sure `head` is a valid pointer.
    pub(crate) fn from_list_head_ptr(head: *const ListHead<T>) -> Self {
        Self {
            current: head,
            _marker: Default::default(),
        }
    }

    /// Moves the cursor to the next element of the `CircularList`.
    pub fn move_next(&mut self) {
        unsafe {
            // SAFETY: Invariants (2), (3) and (4) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).next;
        }
    }

    /// Moves the cursor to the previous element of the `CircularList`.
    pub fn move_prev(&mut self) {
        unsafe {
            // SAFETY: Invariants (2), (3) and (4) assert that `self.current` is a valid pointer to
            // a valid circular linked list
            self.current = (*self.current).prev;
        }
    }

    /// Returns the value of the list element behind the cursor.
    pub fn value(&self) -> &T {
        // SAFETY: Invariant (4) asserts that `current` is a valid pointer to a `ListHead<T>`.
        unsafe { &(*self.current).value }
    }
}

impl<'life, T: std::fmt::Debug> std::fmt::Debug for Cursor<'life, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value().fmt(f)
    }
}

impl<'life, T: std::fmt::Display> std::fmt::Display for Cursor<'life, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value().fmt(f)
    }
}

impl<'life, T> std::cmp::PartialEq for Cursor<'life, T> {
    fn eq(&self, other: &Self) -> bool {
        self.current == other.current
    }
}
