use std::mem::MaybeUninit;

/// A trait for types having a finite number of possible states.
///
/// Each state of a type implementing this trait is indexed by an integer from `0` to [`Self::NUM_STATES`].
/// This traits provides methods for converting between values of the type and their indices.
pub trait State: Sized {
    /// The total number of distinct states that values of this type can represent.
    ///
    /// The states of the type are associated with unique indices from `0` up to but not including [`Self::NUM_STATES`].
    /// This means [`Self::NUM_STATES`] gives the count of the distinct states of the type.
    ///
    /// # Example
    /// ```
    /// use state_set::*;
    ///
    /// assert_eq!(<()>::NUM_STATES, 1);
    /// assert_eq!(bool::NUM_STATES, 2);
    /// assert_eq!(Option::<bool>::NUM_STATES, 3);
    /// assert_eq!(<(bool, Option<bool>)>::NUM_STATES, 6);
    /// assert_eq!(<[bool; 3]>::NUM_STATES, 8);
    /// ```
    const NUM_STATES: u32;

    /// A compile-time check to ensure that the number of states does not exceed 64.
    ///
    /// If [`Self::NUM_STATES`] is greater than 64, using this will fail to compile.
    ///
    /// # Example
    /// ```
    /// use state_set::*;
    ///
    /// <[bool; 5]>::CHECK_NUM_STATES_AT_MOST_64; // 2^5 = 32 <= 64
    /// <[bool; 6]>::CHECK_NUM_STATES_AT_MOST_64; // 2^6 = 64 <= 64
    /// ```
    ///
    /// ```compile_fail
    /// use state_set::*;
    ///
    /// <[bool; 7]>::CHECK_NUM_STATES_AT_MOST_64; // 2^7 = 128 > 64
    /// ```
    const CHECK_NUM_STATES_AT_MOST_64: () = {
        let _ = 64 - Self::NUM_STATES;
    };

    /// Converts `self` into an index, which is an integer from `0` to `Self::NUM_STATES - 1`.
    ///
    /// # Examples
    ///
    /// ```
    /// use state_set::*;
    ///
    /// assert_eq!(false.into_index(), 0);
    /// assert_eq!(true.into_index(), 1);
    /// ```
    fn into_index(self) -> u32;

    /// Converts `index` into a value of this type. Returns `None` if `index >= Self::STATUS`.
    ///
    /// # Examples
    ///
    /// ```
    /// use state_set::*;
    ///
    /// assert_eq!(bool::from_index(0), Some(false));
    /// assert_eq!(bool::from_index(1), Some(true));
    /// assert_eq!(bool::from_index(2), None);
    /// ```
    #[inline]
    fn from_index(index: u32) -> Option<Self> {
        // SAFETY: `index` is less than `Self::NUM_STATES`.
        (index < Self::NUM_STATES).then(|| unsafe { Self::from_index_unchecked(index) })
    }

    /// Converts `index` into a value of this type without checking that `index` is valid.
    ///
    /// # Safety
    /// The caller must ensure that `index` is less than [`Self::NUM_STATES`].
    ///
    /// # Examples
    ///
    /// ```
    /// use state_set::*;
    ///
    /// assert_eq!(unsafe { bool::from_index(0) }, Some(false));
    /// assert_eq!(unsafe { bool::from_index(1) }, Some(true));
    unsafe fn from_index_unchecked(index: u32) -> Self;
}

impl State for bool {
    const NUM_STATES: u32 = 2;

    #[inline]
    fn into_index(self) -> u32 {
        self as u32
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        index != 0
    }
}

impl<T: State, const N: usize> State for [T; N] {
    const NUM_STATES: u32 = T::NUM_STATES.pow(N as u32);

    #[inline]
    fn into_index(self) -> u32 {
        self.into_iter()
            .fold(0, |index, state| index * T::NUM_STATES + state.into_index())
    }

    #[inline]
    unsafe fn from_index_unchecked(mut index: u32) -> Self {
        let mut array: [MaybeUninit<T>; N] = MaybeUninit::uninit().assume_init();
        for state in array.iter_mut().rev() {
            state.write(T::from_index_unchecked(index % T::NUM_STATES));
            index /= T::NUM_STATES;
        }

        // The following is equivalent to `std::mem::transmute::<_, [T; N]>(states)`,
        // which doesn't compile on Rust 1.69.0.
        // Reference: https://github.com/rust-lang/rust/issues/61956
        let res = (&mut array as *mut _ as *mut [T; N]).read();
        core::mem::forget(array);
        res
    }
}

macro_rules! tuple_impl {
    ($($T:ident)*) => {
        impl<$($T: State),*> State for ($($T,)*) {
            const NUM_STATES: u32 = 1 $(* $T::NUM_STATES)*;

            #[allow(non_snake_case, unconditional_recursion, unused_mut, unused_parens)]
            #[inline]
            fn into_index(self) -> u32 {
                let ($($T),*) = self;
                let mut index = 0;
                $(
                    index = index * $T::NUM_STATES + $T.into_index();
                )*
                index
            }

            #[allow(unused_assignments, unused_mut, unused_variables, clippy::unused_unit)]
            #[inline]
            unsafe fn from_index_unchecked(mut index: u32) -> Self {
                let mut base = Self::NUM_STATES;
                ($(
                    {
                        base /= $T::NUM_STATES;
                        let value = <$T>::from_index_unchecked(index / base);
                        index %= base;
                        value
                    },
                )*)
            }
        }
    };
}

tuple_impl!();
tuple_impl!(A);
tuple_impl!(A B);
tuple_impl!(A B C);
tuple_impl!(A B C D);
tuple_impl!(A B C D E);
tuple_impl!(A B C D E F);
tuple_impl!(A B C D E F G);
tuple_impl!(A B C D E F G H);
tuple_impl!(A B C D E F G H I);
tuple_impl!(A B C D E F G H I J);
tuple_impl!(A B C D E F G H I J K);
tuple_impl!(A B C D E F G H I J K L);
tuple_impl!(A B C D E F G H I J K L M);
tuple_impl!(A B C D E F G H I J K L M N);
tuple_impl!(A B C D E F G H I J K L M N O);
tuple_impl!(A B C D E F G H I J K L M N O P);

macro_rules! singleton_impl {
    ($ty:ty) => {
        impl State for $ty {
            const NUM_STATES: u32 = 1;

            #[inline]
            fn into_index(self) -> u32 {
                0
            }

            #[inline]
            unsafe fn from_index_unchecked(_index: u32) -> Self {
                Self
            }
        }
    };
}

macro_rules! enum_impl {
    ($ty:ty, $states:expr $(, $variant:ident = $index:expr)*) => {
        impl State for $ty {
            const NUM_STATES: u32 = $states;

            #[inline]
            fn into_index(self) -> u32 {
                match self {
                    $(Self::$variant => $index,)*
                }
            }

            #[inline]
            unsafe fn from_index_unchecked(index: u32) -> Self {
                match index {
                    $($index => Self::$variant,)*
                    _ => unreachable!(),
                }
            }
        }
    };
}

impl<T: State> State for Option<T> {
    const NUM_STATES: u32 = 1 + T::NUM_STATES;

    #[inline]
    fn into_index(self) -> u32 {
        self.map_or(0, |x| 1 + x.into_index())
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        (index > 0).then(|| T::from_index_unchecked(index - 1))
    }
}

impl<T: State, E: State> State for Result<T, E> {
    const NUM_STATES: u32 = T::NUM_STATES + E::NUM_STATES;

    #[inline]
    fn into_index(self) -> u32 {
        self.map_or_else(|e| T::NUM_STATES + e.into_index(), |v| v.into_index())
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        if index < T::NUM_STATES {
            Self::Ok(T::from_index_unchecked(index))
        } else {
            Self::Err(E::from_index_unchecked(index - T::NUM_STATES))
        }
    }
}

// std::alloc
singleton_impl!(std::alloc::System);

// std::cmp
impl<T: State> State for std::cmp::Reverse<T> {
    const NUM_STATES: u32 = T::NUM_STATES;

    #[inline]
    fn into_index(self) -> u32 {
        Self::NUM_STATES - self.0.into_index() - 1
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        Self(T::from_index_unchecked(Self::NUM_STATES - index - 1))
    }
}

enum_impl!(std::cmp::Ordering, 3, Less = 0, Equal = 1, Greater = 2);

// std::convert
enum_impl!(std::convert::Infallible, 0);

// std::fmt
singleton_impl!(std::fmt::Error);
enum_impl!(std::fmt::Alignment, 3, Left = 0, Right = 1, Center = 2);

// std::marker
impl<T> State for std::marker::PhantomData<T>
where
    T: ?Sized,
{
    const NUM_STATES: u32 = 1;

    #[inline]
    fn into_index(self) -> u32 {
        0
    }

    #[inline]
    unsafe fn from_index_unchecked(_index: u32) -> Self {
        Self
    }
}

singleton_impl!(std::marker::PhantomPinned);

// std::net
enum_impl!(std::net::Shutdown, 3, Read = 0, Write = 1, Both = 2);

// std::num
enum_impl!(
    std::num::FpCategory,
    5,
    Nan = 0,
    Infinite = 1,
    Zero = 2,
    Subnormal = 3,
    Normal = 4
);

// std::ops
impl<B: State, C: State> State for std::ops::ControlFlow<B, C> {
    const NUM_STATES: u32 = B::NUM_STATES + C::NUM_STATES;

    #[inline]
    fn into_index(self) -> u32 {
        match self {
            Self::Continue(c) => c.into_index(),
            Self::Break(b) => C::NUM_STATES + b.into_index(),
        }
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        if index < C::NUM_STATES {
            Self::Continue(C::from_index_unchecked(index))
        } else {
            Self::Break(B::from_index_unchecked(index - C::NUM_STATES))
        }
    }
}

#[cfg(test)]
mod test {
    use std::fmt::Debug;

    use super::*;

    fn check<T: Clone + Debug + PartialEq + State>(states: &[T]) {
        assert_eq!(T::NUM_STATES, states.len() as u32);
        for (i, state) in states.iter().enumerate() {
            assert_eq!(state.clone().into_index(), i as u32);
            assert_eq!(T::from_index(i as u32), Some(state.clone()));
        }
        assert_eq!(T::from_index(states.len() as u32), None);
    }

    #[test]
    fn bool() {
        check(&[false, true]);
    }

    #[test]
    fn tuple() {
        check(&[()]);
        check(&[(false), (true)]);
        check(&[(false, false), (false, true), (true, false), (true, true)]);
        check(&[
            (false, (), false),
            (false, (), true),
            (true, (), false),
            (true, (), true),
        ]);
        check(&[
            ((), (false), (false, false)),
            ((), (false), (false, true)),
            ((), (false), (true, false)),
            ((), (false), (true, true)),
            ((), (true), (false, false)),
            ((), (true), (false, true)),
            ((), (true), (true, false)),
            ((), (true), (true, true)),
        ]);
    }

    #[test]
    fn array() {
        check(&[[false, false], [false, true], [true, false], [true, true]]);
    }

    #[test]
    fn array_states() {
        assert_eq!(<[bool; 0]>::NUM_STATES, 1);
        assert_eq!(<[bool; 1]>::NUM_STATES, 2);
        assert_eq!(<[bool; 10]>::NUM_STATES, 1024);
        assert_eq!(<[bool; 31]>::NUM_STATES, 1 << 31);
    }

    #[test]
    fn option() {
        check(&[None, Some(false), Some(true)]);
    }

    #[test]
    fn result() {
        type Result = std::result::Result<bool, Option<bool>>;
        check(&[
            Result::Ok(false),
            Result::Ok(true),
            Result::Err(None),
            Result::Err(Some(false)),
            Result::Err(Some(true)),
        ]);
    }

    #[test]
    fn std_alloc_system() {
        use std::alloc::System;
        assert_eq!(System.into_index(), 0);
        assert!(System::from_index(0).is_some());
        assert!(System::from_index(1).is_none());
    }

    #[test]
    fn std_cmp_reverse() {
        use std::cmp::Reverse;
        check(&[Reverse(true), Reverse(false)]);
    }

    #[test]
    fn std_cmp_ordering() {
        use std::cmp::Ordering;
        check(&[Ordering::Less, Ordering::Equal, Ordering::Greater]);
    }

    #[test]
    fn std_convert_infallible() {
        check::<std::convert::Infallible>(&[]);
    }

    #[test]
    fn std_fmt_error() {
        check(&[std::fmt::Error]);
    }

    #[test]
    fn std_marker_phantom_data() {
        check(&[std::marker::PhantomData::<usize>]);
    }

    #[test]
    fn std_num_fp_category() {
        use std::num::FpCategory::*;
        check(&[Nan, Infinite, Zero, Subnormal, Normal]);
    }

    #[test]
    fn std_ops_control_flow() {
        use std::ops::ControlFlow::*;
        check(&[Continue(false), Continue(true), Break(false), Break(true)]);
    }
}
