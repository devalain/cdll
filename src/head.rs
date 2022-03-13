use std::{marker::PhantomData, ptr};

/// List element for a doubly linked list.
pub struct ListHead<T> {
    next: *const ListHead<T>,
    prev: *const ListHead<T>,
    value: T,
}

impl<T> ListHead<T> {
    /// Creates a new element with value `val`.
    /// The created element is its own previous and next element.
    /// # Layout
    /// ┌───┐
    /// │   │
    /// │ ┌─▼──┐
    /// └─┤val ├─┐
    ///   └──▲─┘ │
    ///      │   │
    ///      └───┘
    pub fn init(val: T) -> Box<Self> {
        let mut new = Box::new(Self {
            next: ptr::null(),
            prev: ptr::null(),
            value: val,
        });
        new.next = &*new;
        new.prev = &*new;
        new
    }

    /// Get a pointer to the next element.
    pub fn next(&self) -> *const Self {
        self.next
    }

    /// Get a pointer to the previous element.
    pub fn prev(&self) -> *const Self {
        self.prev
    }

    /// Insert `new` between `prev` and `next`.
    unsafe fn __add(new: *mut Self, prev: *mut Self, next: *mut Self) {
        /*
           ┌────┬──►┌────┬──►┌────┐
           │prev│   │new │   │next│
           └────┘◄──┴────┘◄──┴────┘
        */
        (*next).prev = new;
        (*new).next = next;
        (*new).prev = prev;
        (*prev).next = new;
    }

    /// Disconnect an element by connecting its previous and next elements together.
    unsafe fn __del(prev: *mut Self, next: *mut Self) {
        /*
            ┌────┬──►┌────┐
            │prev│   │next│
            └────┘◄──┴────┘
        */
        (*next).prev = prev;
        (*prev).next = next;
    }

    /// Disconnect an element from the list then get its value and a pointer to the next element.
    /// The `ListHead` is dropped in the process.
    unsafe fn __del_entry(to_del: *mut Self) -> (*const Self, T) {
        let mut next = (*to_del).next;
        if to_del as *const _ != next {
            Self::__del((*to_del).prev as *mut _, (*to_del).next as *mut _);
        } else {
            next = ptr::null();
        }
        let to_del = Box::from_raw(to_del);
        (next, to_del.value)
    }

    /// Insert an element behind this one.
    pub fn add(&mut self, new: &mut Self) {
        unsafe {
            // SAFETY: Since `self` and `new` are borrow checked references, it must be true that
            // the `new` and `next` parameters are valid pointers. As for the `prev` parameters,
            // it is the same as `self` or another valid pointer if other calls `__add` where
            // issued previously.
            Self::__add(new, self.prev as *mut _, self);
        }
    }

    /// Delete an element.
    ///
    /// # Safety
    /// The calling party must assert that the `to_del` pointer is aligned and not dangling.
    pub unsafe fn del(to_del: *mut Self) -> (*const Self, T) {
        Self::__del_entry(to_del)
    }

    /// Connect `new` in place of `old` in the list.
    unsafe fn __replace(old: *mut Self, new: *mut Self) {
        (*new).next = (*old).next;
        (*((*new).next as *mut Self)).prev = new;
        (*new).prev = (*old).prev;
        (*((*new).prev as *mut Self)).next = new;
    }

    /// Exchange 2 elements by interchanging their connection to the list.
    pub unsafe fn swap(entry1: *mut Self, entry2: *mut Self) {
        let mut pos = (*entry2).prev;
        Self::__del((*entry2).prev as *mut _, (*entry2).next as *mut _);
        Self::__replace(entry1, entry2);
        if pos == entry1 {
            pos = entry2;
        }
        Self::__add(entry1 as *mut _, pos as *mut _, (*pos).next as *mut _);
    }

    /// Insert `list` between `prev` and `next`.
    pub unsafe fn add_list(list: *mut Self, prev: *mut Self, next: *mut Self) {
        let last_of_list = (*list).prev as *mut Self;

        (*next).prev = last_of_list;
        (*last_of_list).next = next;

        (*list).prev = prev;
        (*prev).next = list;
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
        // SAFETY: the lifetime `'life` of `self` is the same as the lifetime of the list. We
        // return a `'life` shared reference to the current value which is bound to the list.
        // Plus, the list is circular so next should always be non null if the list is non empty.
        let (current, next) = unsafe {
            let r = &*self.next;
            (&r.value, (*r).next)
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
        let (current, next) = unsafe {
            let r = &mut *self.next;
            (&mut r.value, (*r).next as *mut _)
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
