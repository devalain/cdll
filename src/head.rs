use std::{marker::PhantomData, ptr};

/// List element.
pub struct ListHead<T> {
    next: *const ListHead<T>,
    prev: *const ListHead<T>,
    value: T,
}

impl<T> ListHead<T> {
    /// Creates a new element with value `val`.
    /// The created element is its own previous and next element.
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
    unsafe fn __del(prev: *mut Self, next: *mut Self) {
        /*
            ┌────┬──►┌────┐
            │prev│   │next│
            └────┘◄──┴────┘
        */
        (*next).prev = prev;
        (*prev).next = next;
    }
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
            Self::__add(new, self.prev as *mut Self, self);
        }
    }

    /// Delete an element.
    ///
    /// # Safety
    /// The calling party must assert that the `to_del` pointer is aligned and not dangling.
    pub unsafe fn del(to_del: *mut Self) -> (*const Self, T) {
        Self::__del_entry(to_del)
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
