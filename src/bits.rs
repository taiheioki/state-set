use core::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Not, Shl, ShlAssign, Shr,
    ShrAssign,
};

pub trait Bits:
    Sized
    + Eq
    + BitAnd<Output = Self>
    + BitAndAssign
    + BitOr<Output = Self>
    + BitOrAssign
    + BitXor<Output = Self>
    + BitXorAssign
    + Not<Output = Self>
    + Shl<u32, Output = Self>
    + ShlAssign<u32>
    + Shr<u32, Output = Self>
    + ShrAssign<u32>
{
    const BITS: u32;
    const ZERO: Self;
    const FULL: Self;

    fn is_zero(&self) -> bool;

    fn set_zero(&mut self);

    fn count_ones(&self) -> u32;

    fn leading_zeros(&self) -> u32;

    fn trailing_zeros(&self) -> u32;

    fn get_bit(&self, index: u32) -> Option<bool>;

    fn set_bit(&mut self, index: u32);

    fn unset_bit(&mut self, index: u32);
}

macro_rules! generate_bits_impl {
    ($ty: ty) => {
        impl Bits for $ty {
            const BITS: u32 = Self::BITS;
            const ZERO: Self = 0;
            const FULL: Self = Self::MAX;

            fn is_zero(&self) -> bool {
                *self == 0
            }

            fn set_zero(&mut self) {
                *self = 0
            }

            fn count_ones(&self) -> u32 {
                self.count_ones()
            }

            fn leading_zeros(&self) -> u32 {
                self.leading_zeros()
            }

            fn trailing_zeros(&self) -> u32 {
                self.trailing_ones()
            }

            fn get_bit(&self, index: u32) -> Option<bool> {
                (index < Self::BITS).then(|| (*self >> index) & 1 == 1)
            }

            fn set_bit(&mut self, index: u32) {
                *self |= 1 << index;
            }

            fn unset_bit(&mut self, index: u32) {
                *self &= !(1 << index);
            }
        }
    };
}

generate_bits_impl!(u8);
generate_bits_impl!(u16);
generate_bits_impl!(u32);
generate_bits_impl!(u64);
generate_bits_impl!(u128);
