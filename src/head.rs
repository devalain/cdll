use std::{marker::PhantomData, ptr};

/// List element for a doubly linked list.
pub struct ListHead<T> {
    next: *const ListHead<T>,
    prev: *const ListHead<T>,
    value: T,
}

// The present implementation aims to preserve the following invariant (3):
// * The `next` and `prev` pointers are always valid
// * Following the `next` field recursively must always end up to the original `Self`
// * Following the `prev` field recursively must give the exact reverse path as the `next` one
impl<T> ListHead<T> {
    /// Creates a new element with value `val`.
    /// The created element is its own previous and next element.
    /// # Layout
    /// ```text
    /// ┌───┐
    /// │   │
    /// │ ┌─▼──┐
    /// └─┤val ├─┐
    ///   └──▲─┘ │
    ///      │   │
    ///      └───┘
    /// ```
    pub fn new(val: T) -> Box<Self> {
        let mut new = Box::new(Self {
            next: ptr::null(),
            prev: ptr::null(),
            value: val,
        });

        // Preserving invariant (3)
        new.next = &*new;
        new.prev = &*new;

        new
    }

    /// Gets a pointer to the next element.
    pub fn next(&self) -> *const Self {
        self.next
    }

    /// Gets a pointer to the previous element.
    pub fn prev(&self) -> *const Self {
        self.prev
    }

    /// Inserts `new` between `prev` and `next`.
    ///
    /// # Sketch
    /// ```text
    /// ┌────┬──►┌────┬──►┌────┐
    /// │prev│   │new │   │next│
    /// └────┘◄──┴────┘◄──┴────┘
    /// ```
    ///
    /// # Safety
    /// * `next`, `new` and `prev` must be valid pointers.
    /// * `new` must be disconnected from its old place (i.e. with `__del` or `__replace`) before
    /// calling this function otherwise it would break invariant (3).
    unsafe fn __add(new: *mut Self, prev: *mut Self, next: *mut Self) {
        (*next).prev = new;
        (*new).next = next;
        (*new).prev = prev;
        (*prev).next = new;
    }

    /// Disconnects element(s) by connecting the previous and next elements together.
    ///
    /// # Sketch
    /// ```text
    ///      ┌────┬──┐
    ///      │list│  │
    ///  ┌───┴────┘  │
    /// ┌▼───┬──►┌───▼┐
    /// │prev│   │next│
    /// └────┘◄──┴────┘
    /// ```
    /// # Safety
    /// * `next` and `prev` must be valid pointers.
    /// * the element(s) between `next` and `prev` must be dropped or connected somewhere else
    /// after calling this function in order to preserve invariant (3).
    unsafe fn __del(prev: *mut Self, next: *mut Self) {
        (*next).prev = prev;
        (*prev).next = next;
    }

    /// Disconnects an element from the list then returns its value and a pointer to the
    /// next element. The `ListHead` is dropped in the process.
    ///
    /// # Safety
    /// `to_del` must be a valid pointer to a `ListHead` with valid pointers to its next
    /// and previous elements.
    unsafe fn __del_entry(to_del: *mut Self) -> (*const Self, T) {
        let mut next = (*to_del).next;
        if to_del as *const _ != next {
            // `(*to_del).prev` and `(*to_del).next` should be valid according to invariant (3).
            Self::__del((*to_del).prev as *mut _, (*to_del).next as *mut _);
        } else {
            next = ptr::null();
        }

        // `to_del` has to be dropped in order to preserve invariant (3).
        let to_del = Box::from_raw(to_del);
        (next, to_del.value)
    }

    /// Inserts an element behind this one.
    pub fn add(&mut self, new: &mut Self) {
        unsafe {
            // SAFETY: Since `self` and `new` are borrow checked references, it must be true that
            // they are valid pointers. As for the `prev` parameter, it is the same as `self` or
            // another valid pointer according to invariant (3).
            Self::__add(new, self.prev as *mut _, self);
        }
    }

    /// Deletes an element.
    ///
    /// # Safety
    /// The calling party must assert that the `to_del` pointer is valid.
    pub unsafe fn del(to_del: *mut Self) -> (*const Self, T) {
        Self::__del_entry(to_del)
    }

    /// Connects `new` in place of `old` in the list.
    ///
    /// # Sketch
    ///
    /// ## Before
    /// ```text
    ///     ┌────┬──►?
    ///     │new │
    /// ?◄──┴────┘
    /// ┌────┬──►┌────┬──►┌────┐
    /// │prev│   │old │   │next│
    /// └────┘◄──┴────┘◄──┴────┘
    /// ```
    ///
    /// ## After
    /// ```text
    /// ┌───────►┌────┬───────┐
    /// │        │new │       │
    /// │   ┌────┴────┘◄──┐   │
    /// │   │             │   │
    /// ├───▼┐   ┌────┬──►├───▼┐
    /// │prev│   │old │   │next│
    /// └────┘◄──┴────┘   └────┘
    /// ```
    ///
    /// # Safety
    /// * `old` and `next` must be valid pointers
    /// * `old` has to be dropped or connected somewhere else after calling this function in
    /// order to preserve invariant (3).
    unsafe fn __replace(old: *mut Self, new: *mut Self) {
        (*new).next = (*old).next;
        (*((*new).next as *mut Self)).prev = new;
        (*new).prev = (*old).prev;
        (*((*new).prev as *mut Self)).next = new;
    }

    /// Exchanges 2 elements by interchanging their connection to their list (which could be not
    /// the same).
    ///
    /// # Safety
    /// `entry1` and `entry2` must be valid pointers to valid circular linked lists.
    pub unsafe fn swap(entry1: *mut Self, entry2: *mut Self) {
        // `(*entry2).prev` and `(*entry2).next` should be valid according to invariant (3)
        let mut pos = (*entry2).prev;
        Self::__del((*entry2).prev as *mut _, (*entry2).next as *mut _);

        // `entry2` is connected in place of `entry1` which preserve invariant (3).
        Self::__replace(entry1, entry2);

        // in case `entry1` was already behind `entry2`, it is place next to it.
        if pos == entry1 {
            pos = entry2;
        }

        // `pos` and `(*pos).next` are valid according to invariant (3) and `entry1` was just
        // disconnected from its old place.
        Self::__add(entry1 as *mut _, pos as *mut _, (*pos).next as *mut _);
    }

    /// Insert `list` before `next`.
    ///
    /// # Safety
    /// * `list` must be a valid pointer and be part of a valid circular list
    /// * Idem for `next`
    /// * `list` **must not** be an element of the same circular list as `next` without defining a
    /// new head for the orphaned list, otherwise it would cause a memory leak.
    pub unsafe fn add_list(list: *mut Self, next: *mut Self) {
        // `last_of_list` should be valid according to invariant (3)
        let last_of_list = (*list).prev as *mut Self;
        // idem
        let prev = (*next).prev as *mut Self;

        // Preserving invariant (3): as soon as `list` is part of a valid circular list as well as
        // `next`, the connections made here will create 1 or 2 valid circular list(s).

        (*next).prev = last_of_list;
        (*last_of_list).next = next; // The end of `list` is connected to `next`

        (*list).prev = prev;
        (*prev).next = list; // The beginning of `list` is connected to the element before `next`
    }
}

/// Circular list iterator.
pub struct Iter<'life, T> {
    next: *const ListHead<T>,
    _marker: PhantomData<&'life T>,
}
impl<'life, T> Iterator for Iter<'life, T> {
    type Item = &'life T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: the lifetime `'life` of `self` is bound to the lifetime of the list. We
        // return a `'life` shared reference to the current value which is bound to the list.
        // Plus, the list is circular so next should always be non null if the list is non empty.
        let (current, next) = unsafe {
            let r = &*self.next;
            (&r.value, r.next)
        };
        self.next = next;
        Some(current)
    }
}
impl<'life, T> Iter<'life, T> {
    pub fn new(first: *const ListHead<T>) -> Self {
        Self {
            next: first,
            _marker: PhantomData::default(),
        }
    }
}

/// Circular list iterator with mutability.
pub struct IterMut<'life, T> {
    next: *mut ListHead<T>,
    _marker: PhantomData<&'life T>,
}
impl<'life, T> Iterator for IterMut<'life, T> {
    type Item = &'life mut T;

    fn next(&mut self) -> Option<Self::Item> {
        // SAFETY: the lifetime `'life` of `self` is bound to the lifetime of the list. We
        // return a `'life` shared reference to the current value which is bound to the list.
        // Plus, the list is circular so next should always be non null if the list is non empty.
        let (current, next) = unsafe {
            let r = &mut *self.next;
            (&mut r.value, r.next as *mut _)
        };
        self.next = next;
        Some(current)
    }
}
impl<'life, T> IterMut<'life, T> {
    pub fn new(first: *mut ListHead<T>) -> Self {
        Self {
            next: first,
            _marker: PhantomData::default(),
        }
    }
}

// TODO https://doc.rust-lang.org/std/collections/linked_list/struct.Cursor.html
// TODO https://doc.rust-lang.org/std/collections/linked_list/struct.LinkedList.html
#[derive(Clone, Copy, PartialEq)]
pub struct Cursor<'life, T> {
    current: *const ListHead<T>,
    _marker: PhantomData<&'life T>,
}

impl<'life, T> std::ops::Deref for Cursor<'life, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        unsafe { &(*self.current).value }
    }
}
impl<'life, T: std::fmt::Debug> std::fmt::Debug for Cursor<'life, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (&**self).fmt(f)
    }
}
impl<'life, T: std::fmt::Display> std::fmt::Display for Cursor<'life, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        (&**self).fmt(f)
    }
}
impl<'life, T> From<*const ListHead<T>> for Cursor<'life, T> {
    fn from(head: *const ListHead<T>) -> Self {
        Self {
            current: head,
            _marker: Default::default(),
        }
    }
}
