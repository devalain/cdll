use {crate::CircularList, alloc::boxed::Box, core::ptr::NonNull};

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

    pub(crate) unsafe fn half(list: &CircularList<T>) -> Option<(NonNull<Self>, usize)> {
        let head = list.head?;
        let mut mid_idx = 0;
        unsafe {
            let mut slow = head;
            let mut fast = (*head.as_ptr()).next;
            while fast != head && (*fast.as_ptr()).next != head {
                fast = (*(*fast.as_ptr()).next.as_ptr()).next;
                if fast != head {
                    slow = (*slow.as_ptr()).next;
                    mid_idx += 1;
                }
            }
            Some(((*slow.as_ptr()).next, (mid_idx + 1) % list.len))
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

    pub(crate) unsafe fn merge(
        head_a: NonNull<Node<T>>,
        head_b: NonNull<Node<T>>,
    ) -> NonNull<Node<T>>
    where
        T: PartialOrd,
    {
        unsafe {
            let lt = |a: NonNull<Node<T>>, b: NonNull<Node<T>>| {
                (*a.as_ptr()).value < (*b.as_ptr()).value
            };

            let tail_a = (*head_a.as_ptr()).prev;
            let tail_b = (*head_b.as_ptr()).prev;

            let head = if lt(head_a, head_b) { head_a } else { head_b };
            let tail = if lt(tail_a, tail_b) { tail_b } else { tail_a };

            let mut next_a = if head == head_a {
                (*head_a.as_ptr()).next
            } else {
                head_a
            };
            let mut next_b = if head == head_b {
                (*head_b.as_ptr()).next
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
                    next_a = (*next_a.as_ptr()).next;
                } else {
                    Self::connect(current, next_b);
                    if next_b == tail_b {
                        Self::connect(next_b, next_a);
                        break;
                    }
                    next_b = (*next_b.as_ptr()).next;
                }
                current = (*current.as_ptr()).next;
            }

            Node::connect(tail, head);
            head
        }
    }
}
