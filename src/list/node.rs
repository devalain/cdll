use core::ptr::NonNull;

use crate::CircularList;

pub(crate) struct Node<T> {
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
    pub(crate) fn new(value: T) -> NonNull<Self> {
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

    pub(crate) unsafe fn next_distinct(this: NonNull<Node<T>>) -> Option<NonNull<Node<T>>> {
        unsafe {
            let next = (*this.as_ptr()).next;
            if next != this { Some(next) } else { None }
        }
    }

    pub(crate) unsafe fn insert_prev(this: NonNull<Node<T>>, val: T) {
        let new = Self::new(val);

        unsafe {
            let prev = (*this.as_ptr()).prev.as_ptr();
            (*prev).next = new;
            (*new.as_ptr()).prev = NonNull::new_unchecked(prev);

            (*new.as_ptr()).next = NonNull::new_unchecked(this.as_ptr());
            (*this.as_ptr()).prev = new;
        }
    }

    pub(crate) unsafe fn disconnect(this: NonNull<Node<T>>) {
        unsafe {
            let prev = (*this.as_ptr()).prev.as_ptr();
            let next = (*this.as_ptr()).next.as_ptr();

            if prev != next {
                // 3 or more elements
                let prev = (*this.as_ptr()).prev;
                let next = (*this.as_ptr()).next;

                (*prev.as_ptr()).next = next;
                (*next.as_ptr()).prev = prev;
            } else if this.as_ptr() != prev {
                // 2 elements
                let next = (*this.as_ptr()).next;

                (*next.as_ptr()).next = next;
                (*next.as_ptr()).prev = next;
            };
        }
    }

    pub(crate) unsafe fn connect(this: NonNull<Node<T>>, next: NonNull<Node<T>>) {
        unsafe {
            (*this.as_ptr()).next = next;
            (*next.as_ptr()).prev = this;
        }
    }

    pub(crate) unsafe fn remove(this: NonNull<Node<T>>) -> T {
        unsafe {
            Self::disconnect(this);
            let this = Box::from_raw(this.as_ptr());
            this.value
        }
    }

    pub(crate) unsafe fn half(list: &CircularList<T>) -> Option<NonNull<Self>> {
        let head = list.head?;
        unsafe {
            let mut slow = head;
            let mut fast = (*head.as_ptr()).next;
            while fast != head && (*fast.as_ptr()).next != head {
                fast = (*(*fast.as_ptr()).next.as_ptr()).next;
                if fast != head {
                    slow = (*slow.as_ptr()).next;
                }
            }
            Some((*slow.as_ptr()).next)
        }
    }

    pub(crate) unsafe fn split(head: NonNull<Node<T>>, mid: NonNull<Node<T>>) {
        unsafe {
            // Assume mid is not head
            let old_last = (*head.as_ptr()).prev;
            let new_last = (*mid.as_ptr()).prev;

            (*head.as_ptr()).prev = new_last;
            (*mid.as_ptr()).prev = old_last;

            (*old_last.as_ptr()).next = mid;
            (*new_last.as_ptr()).next = head;
        }
    }
}
