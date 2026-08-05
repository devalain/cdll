use core::ptr::NonNull;

pub(super) struct Node<T> {
    pub next: NonNull<Node<T>>,
    pub prev: NonNull<Node<T>>,
    pub value: T,
}
impl<T> Node<T> {
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
    pub(super) fn new(value: T) -> NonNull<Self> {
        let boxed = Box::new(Node {
            next: NonNull::dangling(),
            prev: NonNull::dangling(),
            value,
        });

        let mut ptr = NonNull::from(Box::leak(boxed));

        unsafe {
            ptr.as_mut().next = ptr;
            ptr.as_mut().prev = ptr;
        }

        ptr
    }

    pub(super) unsafe fn next_distinct(this: NonNull<Node<T>>) -> Option<NonNull<Node<T>>> {
        unsafe {
            let next = (*this.as_ptr()).next;
            if next != this { Some(next) } else { None }
        }
    }

    pub(super) unsafe fn insert_prev(this: NonNull<Node<T>>, val: T) {
        let new = Self::new(val);

        unsafe {
            let prev = (*this.as_ptr()).prev.as_ptr();
            (*prev).next = new;
            (*new.as_ptr()).prev = NonNull::new_unchecked(prev);

            (*new.as_ptr()).next = NonNull::new_unchecked(this.as_ptr());
            (*this.as_ptr()).prev = new;
        }
    }

    pub(super) unsafe fn remove(this: NonNull<Node<T>>) -> T {
        unsafe {
            let prev = (*this.as_ptr()).prev.as_ptr();
            let next = (*this.as_ptr()).next.as_ptr();

            if prev != next {
                // 3 or more elements
                let this = Box::from_raw(this.as_ptr());
                let prev = this.prev;
                let next = this.next;

                (*prev.as_ptr()).next = next;
                (*next.as_ptr()).prev = prev;

                this.value
            } else if this.as_ptr() == prev {
                // 1 element
                let this = Box::from_raw(this.as_ptr());

                this.value
            } else {
                // 2 elements
                let this = Box::from_raw(this.as_ptr());
                let next = this.next;

                (*next.as_ptr()).next = next;
                (*next.as_ptr()).prev = next;

                this.value
            }
        }
    }
}
