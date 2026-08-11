/// Create a list with provided elements.
/// # Example
/// ```
/// # use cdll::list;
/// let primes = list![2, 3, 5, 7, 11];
/// // println!("{:?}", primes);
/// ```
/// It can also be used with whatever expression that is an `IntoIterator`
/// ```
/// # use cdll::list;
/// let first_hundred_numbers = list![@each 1_i32..=100];
/// let sum: i32 = first_hundred_numbers.iter().copied().sum();
/// assert_eq!(sum, 5050);
/// ```
#[macro_export]
macro_rules! list {
    [$($elem:expr),* $(,)?] => {{
        #[allow(unused_mut)]
        let mut l = $crate::CircularList::default();
        $(
            l.push_back($elem);
        )*
        l
    }};
    [@each $iter:expr] => {{
        $iter.collect::<$crate::CircularList<_>>()
    }};
}
