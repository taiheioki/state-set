use core::mem::MaybeUninit;

use crate::StateSet;

/// A trait for types having a finite number of possible states.
///
/// Types that implement [`State`] have a fixed, known number of possible states that they can represent.
/// For example, a [`bool`] can represent two states (`true` and `false`), so it can implement [`State`]
/// with [`NUM_STATES`](State::NUM_STATES) equal to `2`.
///
/// Implementing [`State`] provides methods for converting between instances of the type and their
/// corresponding indices. The indices are integers from `0` to `NUM_STATES - 1`.
///
/// This trait is typically derived using `#[derive(State)]` rather than implemented manually. When derived,
/// it automatically calculates the total number of states ([`NUM_STATES`](State::NUM_STATES)) and provides methods to convert
/// each state to a unique index ([`into_index`](State::into_index)) and back ([`from_index`](State::from_index)).
///
/// # Examples
///
/// Deriving the `State` trait for an enum:
///
/// ```rust
/// # #[cfg(feature = "alloc")] {
/// # use state_set::*;
/// #[derive(Debug, PartialEq, Eq, State)]
/// enum Direction {
///     North,
///     South,
///     East,
///     West,
/// }
///
/// assert_eq!(Direction::NUM_STATES, 4);
///
/// assert_eq!(Direction::North.into_index(), 0);
/// assert_eq!(Direction::South.into_index(), 1);
/// assert_eq!(Direction::East.into_index(), 2);
/// assert_eq!(Direction::West.into_index(), 3);
///
/// assert_eq!(Direction::from_index(0), Some(Direction::North));
/// assert_eq!(Direction::from_index(1), Some(Direction::South));
/// assert_eq!(Direction::from_index(2), Some(Direction::East));
/// assert_eq!(Direction::from_index(3), Some(Direction::West));
/// assert_eq!(Direction::from_index(4), None);
/// # }
/// ```
///
/// Deriving the `State` trait for a struct:
///
/// ```rust
/// # #[cfg(feature = "alloc")] {
/// # use state_set::*;
/// #[derive(Debug, PartialEq, Eq, State)]
/// struct BooleanTriple {
///     a: bool,
///     b: bool,
///     c: bool,
/// }
///
/// assert_eq!(BooleanTriple::NUM_STATES, 8);
/// assert_eq!(BooleanTriple { a: false, b: false, c: false }.into_index(), 0);
/// assert_eq!(BooleanTriple::from_index(0), Some(BooleanTriple { a: false, b: false, c: false }));
/// # }
/// ```
///
/// # Implementing types
/// This crate implements the [`State`] trait for the following types:
///
/// #### Primitives
/// - [`bool`]
/// - Tuples of up to 16 elements, where each type implements [`State`]
/// - Arrays of a type implementing [`State`]
///
/// #### Core/std library
/// - [`Option<T>`] for any `T` that implements [`State`]
/// - [`Result<T, E>`] for any `T` and `E` that implement [`State`]
/// - [`core::cmp::Ordering`]
/// - [`core::cmp::Reverse<T>`] for any `T` that implements [`State`]
/// - [`core::convert::Infallible`]
/// - [`core::fmt::Error`]
/// - [`core::fmt::Alignment`]
/// - [`core::marker::PhantomData<T>`] for any `T` that implements [`State`]
/// - [`core::marker::PhantomPinned`]
/// - [`core::num::FpCategory`]
/// - [`core::ops::ControlFlow<B, C>`] for any `B` and `C` that implement [`State`]
/// - [`std::alloc::System`] (requires the `std` feature enabled by default)
/// - [`std::net::Shutdown`] (requires the `std` feature enabled by default)
///
/// #### Third-party library
/// - [`either::Either<L, R>`] for any `L` and `R` that implement [`State`] (requires the `either` feature)
/// - [`StateSet<T>`] for any `T` that implements [`State`]
pub trait State: Sized {
    /// The total number of distinct states that values of this type can represent.
    ///
    /// The states of the type are associated with unique indices from `0` up to but not including [`Self::NUM_STATES`].
    /// This means [`Self::NUM_STATES`] gives the count of the distinct states of the type.
    ///
    /// # Example
    /// ```
    /// # use state_set::*;
    /// assert_eq!(<()>::NUM_STATES, 1);
    /// assert_eq!(bool::NUM_STATES, 2);
    /// assert_eq!(Option::<bool>::NUM_STATES, 3);
    /// assert_eq!(<(bool, Option<bool>)>::NUM_STATES, 6);
    /// assert_eq!(<[bool; 3]>::NUM_STATES, 8);
    /// ```
    const NUM_STATES: u32;

    // A compile-time check that `Self::NUM_STATES` is at most 64.
    #[doc(hidden)]
    const CHECK_NUM_STATES_AT_MOST_64: () = {
        let _ = 64 - Self::NUM_STATES;
    };

    /// Converts `self` into an index, which is an integer from `0` to `Self::NUM_STATES - 1`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// # use state_set::*;
    /// #[derive(State)]
    /// enum Enum {
    ///     A,
    ///     B,
    /// }
    ///
    /// assert_eq!(Enum::from_index(Enum::A), 0);
    /// assert_eq!(Enum::from_index(Enum::A), 1);
    /// # }
    /// ```
    #[must_use]
    fn into_index(self) -> u32;

    /// Converts `index` into a value of this type. Returns `None` if `index >= Self::STATUS`.
    ///
    /// # Examples
    ///
    /// ```
    /// # #[cfg(feature = "alloc")] {
    /// # use state_set::*;
    /// #[derive(Debug, PartialEq, Eq, State)]
    /// enum Enum {
    ///     A,
    ///     B,
    /// }
    ///
    /// assert_eq!(Enum::from_index(0), Some(Enum::A));
    /// assert_eq!(Enum::from_index(1), Some(Enum::B));
    /// assert_eq!(Enum::from_index(2), None);
    /// # }
    /// ```
    #[inline]
    #[must_use]
    fn from_index(index: u32) -> Option<Self> {
        // SAFETY: `index` is less than `Self::NUM_STATES`.
        (index < Self::NUM_STATES).then(|| unsafe { Self::from_index_unchecked(index) })
    }

    /// Converts `index` into a value of this type without checking the validity of `index`.
    ///
    /// # Safety
    /// The caller must ensure that `index` is less than [`Self::NUM_STATES`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use state_set::*;
    /// assert_eq!(unsafe { bool::from_index(0) }, Some(false));
    /// assert_eq!(unsafe { bool::from_index(1) }, Some(true));
    #[must_use]
    unsafe fn from_index_unchecked(index: u32) -> Self;

    /// Creates a new [`StateSet<Self>`] consisting of no states.
    ///
    /// # Example
    /// ```
    /// # use state_set::*;
    /// let set = bool::empty_set();
    ///
    /// assert_eq!(set, state_set![]);
    /// ```
    #[inline]
    #[must_use]
    fn empty_set() -> StateSet<Self> {
        StateSet::new()
    }

    /// Creates a new [`StateSet<Self>`] consisting of all the states.
    ///
    /// # Example
    /// ```
    /// # use state_set::*;
    /// let set = bool::all_set();
    ///
    /// assert_eq!(set, state_set![false, true]);
    /// ```
    #[inline]
    #[must_use]
    fn all_set() -> StateSet<Self> {
        !Self::empty_set()
    }
}

impl State for bool {
    const NUM_STATES: u32 = 2;

    #[inline]
    fn into_index(self) -> u32 {
        self.into()
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        index != 0
    }
}

impl<T: State, const N: usize> State for [T; N] {
    #[allow(clippy::cast_possible_truncation)]
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

        // The following is equivalent to `core::mem::transmute::<_, [T; N]>(states)`,
        // which doesn't compile on Rust 1.69.0.
        // Reference: https://github.com/rust-lang/rust/issues/61956
        #[allow(clippy::borrow_as_ptr, clippy::ptr_as_ptr)]
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
        self.map_or_else(|e| T::NUM_STATES + e.into_index(), State::into_index)
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

// core::cmp
impl<T: State> State for core::cmp::Reverse<T> {
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

enum_impl!(core::cmp::Ordering, 3, Less = 0, Equal = 1, Greater = 2);

// core::convert
enum_impl!(core::convert::Infallible, 0);

// core::fmt
singleton_impl!(core::fmt::Error);
enum_impl!(core::fmt::Alignment, 3, Left = 0, Right = 1, Center = 2);

// core::marker
impl<T> State for core::marker::PhantomData<T>
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

singleton_impl!(core::marker::PhantomPinned);

// core::num
enum_impl!(
    core::num::FpCategory,
    5,
    Nan = 0,
    Infinite = 1,
    Zero = 2,
    Subnormal = 3,
    Normal = 4
);

// core::ops
impl<B: State, C: State> State for core::ops::ControlFlow<B, C> {
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

// std::alloc
#[cfg(feature = "std")]
singleton_impl!(std::alloc::System);

// std::net
#[cfg(feature = "std")]
enum_impl!(std::net::Shutdown, 3, Read = 0, Write = 1, Both = 2);

#[cfg(feature = "either")]
impl<L: State, R: State> State for either::Either<L, R> {
    const NUM_STATES: u32 = L::NUM_STATES + R::NUM_STATES;

    #[inline]
    fn into_index(self) -> u32 {
        match self {
            Self::Left(l) => l.into_index(),
            Self::Right(r) => L::NUM_STATES + r.into_index(),
        }
    }

    #[inline]
    unsafe fn from_index_unchecked(index: u32) -> Self {
        if index < L::NUM_STATES {
            Self::Left(L::from_index_unchecked(index))
        } else {
            Self::Right(R::from_index_unchecked(index - L::NUM_STATES))
        }
    }
}

#[cfg(test)]
mod test {
    use core::fmt::Debug;

    use super::*;

    #[allow(clippy::cast_possible_truncation)]
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
        type Result = core::result::Result<bool, Option<bool>>;
        check(&[
            Result::Ok(false),
            Result::Ok(true),
            Result::Err(None),
            Result::Err(Some(false)),
            Result::Err(Some(true)),
        ]);
    }

    #[cfg(feature = "std")]
    #[test]
    fn core_alloc_system() {
        use std::alloc::System;
        assert_eq!(System.into_index(), 0);
        assert!(System::from_index(0).is_some());
        assert!(System::from_index(1).is_none());
    }

    #[test]
    fn core_cmp_reverse() {
        use core::cmp::Reverse;
        check(&[Reverse(true), Reverse(false)]);
    }

    #[test]
    fn core_cmp_ordering() {
        use core::cmp::Ordering;
        check(&[Ordering::Less, Ordering::Equal, Ordering::Greater]);
    }

    #[test]
    fn core_convert_infallible() {
        check::<core::convert::Infallible>(&[]);
    }

    #[test]
    fn core_fmt_error() {
        check(&[core::fmt::Error]);
    }

    #[test]
    fn core_marker_phantom_data() {
        check(&[core::marker::PhantomData::<usize>]);
    }

    #[test]
    fn core_num_fp_category() {
        use core::num::FpCategory::{Infinite, Nan, Normal, Subnormal, Zero};
        check(&[Nan, Infinite, Zero, Subnormal, Normal]);
    }

    #[test]
    fn core_ops_control_flow() {
        use core::ops::ControlFlow::{Break, Continue};
        check(&[Continue(false), Continue(true), Break(false), Break(true)]);
    }

    #[cfg(feature = "either")]
    #[test]
    fn either() {
        use either::Either::{Left, Right};
        check(&[Left(false), Left(true), Right(false), Right(true)]);
    }
}
