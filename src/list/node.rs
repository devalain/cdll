use {crate::CircularList, alloc::boxed::Box, core::ptr::NonNull};

pub(crate) struct Node<T> {
    next: NonNull<Node<T>>,
    prev: NonNull<Node<T>>,
    value: T,
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

    /// Returns the next node.
    pub(crate) unsafe fn next(this: NonNull<Node<T>>) -> NonNull<Node<T>> {
        unsafe { (*this.as_ptr()).next }
    }
    unsafe fn set_next(this: NonNull<Node<T>>, next: NonNull<Node<T>>) {
        unsafe {
            (*this.as_ptr()).next = next;
        }
    }

    /// Returns the previous node.
    pub(crate) unsafe fn prev(this: NonNull<Node<T>>) -> NonNull<Node<T>> {
        unsafe { (*this.as_ptr()).prev }
    }
    unsafe fn set_prev(this: NonNull<Node<T>>, prev: NonNull<Node<T>>) {
        unsafe {
            (*this.as_ptr()).prev = prev;
        }
    }

    /// Returns a shared reference to the value carried by `this` node.
    ///
    /// # Safety
    /// The caller must ensure no exclusive reference lives by the `'a` lifetime.
    pub(crate) unsafe fn value<'a>(this: NonNull<Node<T>>) -> &'a T {
        unsafe { &(*this.as_ptr()).value }
    }

    /// Returns an exclusive reference to the value carried by `this` node.
    ///
    /// # Safety
    /// The caller must ensure no other reference lives by the `'a` lifetime.
    pub(crate) unsafe fn value_mut<'a>(this: NonNull<Node<T>>) -> &'a mut T {
        unsafe { &mut (*this.as_ptr()).value }
    }

    /// Returns the node next to `this`.
    /// Returns `None` if `this` is its own next node.
    pub(crate) unsafe fn next_distinct(this: NonNull<Node<T>>) -> Option<NonNull<Node<T>>> {
        unsafe {
            let next = (*this.as_ptr()).next;
            if next != this { Some(next) } else { None }
        }
    }

    /// Inserts a new node with value `val` between `this` and its previous node.
    pub(crate) unsafe fn insert_prev(this: NonNull<Node<T>>, val: T) {
        let new = Self::new(val);

        unsafe {
            let prev = Self::prev(this);
            Self::set_next(prev, new);
            Self::set_prev(new, prev);

            Self::set_next(new, this);
            Self::set_prev(this, new);
        }
    }

    /// Isolate `this` from its connected nodes (if any).
    /// Do nothing if `this` is only connected to itsef (as it is when constructed
    /// by [`Self::new`]).
    pub(crate) unsafe fn disconnect(this: NonNull<Node<T>>) {
        unsafe {
            let prev = Self::prev(this);
            let next = Self::next(this);

            if prev != next {
                // 3 or more elements
                Self::set_next(prev, next);
                Self::set_prev(next, prev);
            } else if this != prev {
                // 2 elements
                let next = Self::next(this);

                Self::set_next(next, next);
                Self::set_prev(next, next);
            };
            /* The case with 1 element is a no-op */
        }
    }

    /// Sets the next node of `this` to `next` and the previous node of
    /// `next` to `this`.
    ///
    /// # Safety
    /// When using this function, the caller must be careful and make sure
    /// every node is in a group arranged in a circular fashion.
    pub(crate) unsafe fn connect(this: NonNull<Node<T>>, next: NonNull<Node<T>>) {
        unsafe {
            Self::set_next(this, next);
            Self::set_prev(next, this);
        }
    }

    /// Disconnects the node, frees its memory and moves the carried value
    /// by returning it.
    pub(crate) unsafe fn remove(this: NonNull<Node<T>>) -> T {
        unsafe {
            Self::disconnect(this);
            let this = Box::from_raw(this.as_ptr());
            this.value
        }
    }

    pub(super) unsafe fn half(list: &CircularList<T>) -> Option<(NonNull<Self>, usize)> {
        let head = list.head?;
        let mut mid_idx = 0;
        unsafe {
            let mut slow = head;
            let mut fast = Self::next(head);
            while fast != head && Self::next(fast) != head {
                fast = Self::next(Self::next(fast));
                if fast != head {
                    slow = Self::next(slow);
                    mid_idx += 1;
                }
            }
            Some((Self::next(slow), (mid_idx + 1) % list.len))
        }
    }

    pub(super) unsafe fn split(head: NonNull<Node<T>>, mid: NonNull<Node<T>>) {
        unsafe {
            // Assume mid is not head
            let old_last = Node::prev(head);
            let new_last = Node::prev(mid);

            Self::set_prev(head, new_last);
            Self::set_prev(mid, old_last);

            Self::set_next(old_last, mid);
            Self::set_next(new_last, head);
        }
    }

    pub(super) unsafe fn merge(
        head_a: NonNull<Node<T>>,
        head_b: NonNull<Node<T>>,
    ) -> NonNull<Node<T>>
    where
        T: PartialOrd,
    {
        unsafe {
            let lt = |a: NonNull<Node<T>>, b: NonNull<Node<T>>| Self::value(a) < Self::value(b);

            let tail_a = Self::prev(head_a);
            let tail_b = Self::prev(head_b);

            let head = if lt(head_a, head_b) { head_a } else { head_b };
            let tail = if lt(tail_a, tail_b) { tail_b } else { tail_a };

            let mut next_a = if head == head_a {
                Self::next(head_a)
            } else {
                head_a
            };
            let mut next_b = if head == head_b {
                Self::next(head_b)
            } else {
                head_b
            };
            let mut current = head;

            loop {
                if next_a == tail_a && next_b == tail_b {
                    if next_a == tail {
                        Self::connect(current, next_b);
                        Self::connect(next_b, tail);
                    } else {
                        Self::connect(current, next_a);
                        Self::connect(next_a, tail);
                    }
                    break;
                }
                if lt(next_a, next_b) {
                    Self::connect(current, next_a);
                    if next_a == tail_a {
                        Self::connect(next_a, next_b);
                        break;
                    }
                    next_a = Self::next(next_a);
                } else {
                    Self::connect(current, next_b);
                    if next_b == tail_b {
                        Self::connect(next_b, next_a);
                        break;
                    }
                    next_b = Self::next(next_b);
                }
                current = Self::next(current);
            }

            Node::connect(tail, head);
            head
        }
    }
}
