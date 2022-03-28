use {crate::CircularList, core::marker::PhantomData};

/// A trait for sorting elements in [`CircularList`s](`crate::CircularList`).
pub trait Sorter {
    /// The type of the elements to sort.
    type Item: core::cmp::PartialOrd;

    /// Sorts a list of elements that can be ordered.
    fn sort(list: &mut CircularList<Self::Item>);
}

/// Sorts a list of elements that can be ordered.
pub fn sort<T, S>(list: &mut CircularList<T>)
where
    T: core::cmp::PartialOrd,
    S: Sorter<Item = T>,
{
    S::sort(list)
}

/// A merge sort implementation (Found in wikipedia).
pub struct MergeSort<T> {
    _marker: PhantomData<T>,
}

impl<T: core::cmp::PartialOrd> Sorter for MergeSort<T> {
    type Item = T;

    fn sort(list: &mut CircularList<Self::Item>) {
        // Base case. A list of zero or one elements is sorted, by definition.
        if list.len() <= 1 {
            return;
        }

        // Recursive case. First, divide the list into equal-sized sublists
        // consisting of the first half and second half of the list.
        let left = list;
        let mut right = {
            let half_len = left.len() / 2;
            let mut dc = left.double_cursor().expect("The list is not empty");
            for _ in 0..half_len {
                dc.move_next_a();
            }
            dc.split_at_a()
        };

        Self::sort(left);
        Self::sort(&mut right);

        left.merge(right);
    }
}

#[cfg(test)]
mod tests {
    use {
        super::{MergeSort, Sorter},
        crate::list,
    };

    #[test]
    fn merge_sort_works() {
        let mut list = list![3, 1, 8, 21, 5, 9, 12, 5, 2, 6, 6, 6, 13, 2, 17];
        MergeSort::sort(&mut list);
        assert_eq!(
            list.into_iter().collect::<Vec<i32>>(),
            &[1, 2, 2, 3, 5, 5, 6, 6, 6, 8, 9, 12, 13, 17, 21]
        );
    }
}
