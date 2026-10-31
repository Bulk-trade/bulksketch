//! Safe portable arithmetic on canonical polynomial-basis words.
#![forbid(unsafe_code)]

use crate::{field::BinaryField, types::RawProduct};

#[must_use]
#[expect(
    clippy::cast_possible_truncation,
    reason = "split a polynomial into its low and high words"
)]
#[inline]
pub(crate) fn raw_mul<F: BinaryField>(a: u64, b: u64) -> RawProduct {
    debug_assert_eq!((a | b) & !F::MASK, 0, "noncanonical field operand");
    let mut multiples = [0_u128; 16];
    for i in 1_usize..16 {
        multiples[i] = multiples[i & (i - 1)] ^ (u128::from(a) << i.trailing_zeros());
    }
    let mut product = 0_u128;
    for shift in (0..F::BITS).step_by(4) {
        product ^= multiples[((b >> shift) & 15) as usize] << shift;
    }
    RawProduct {
        lo: product as u64,
        hi: (product >> 64) as u64,
    }
}

/// Accepts every 128-bit polynomial, including XOR accumulators of raw products.
#[must_use]
pub(crate) fn reduce<F: BinaryField>(product: RawProduct) -> u64 {
    if F::BITS == 64 {
        // Z^64 = Z^4+Z^3+Z+1. The first fold overflows by at most four bits;
        // folding those again has degree at most seven, so it cannot overflow.
        let high = product.hi;
        let overflow = (high >> 63) ^ (high >> 61) ^ (high >> 60);
        product.lo
            ^ high
            ^ (high << 1)
            ^ (high << 3)
            ^ (high << 4)
            ^ overflow
            ^ (overflow << 1)
            ^ (overflow << 3)
            ^ (overflow << 4)
    } else {
        let mut remainder = 0;
        for word in [product.hi, product.lo] {
            for bit in (0..64).rev() {
                let carry = remainder >> (F::BITS - 1);
                remainder = ((remainder << 1) & F::MASK) | ((word >> bit) & 1);
                remainder ^= F::MODULUS_LOW & 0_u64.wrapping_sub(carry);
            }
        }
        remainder
    }
}

#[must_use]
pub(crate) fn mul<F: BinaryField>(a: u64, b: u64) -> u64 {
    reduce::<F>(raw_mul::<F>(a, b))
}

fn spread(mut word: u64) -> u64 {
    word &= 0xffff_ffff;
    word = (word | (word << 16)) & 0x0000_ffff_0000_ffff;
    word = (word | (word << 8)) & 0x00ff_00ff_00ff_00ff;
    word = (word | (word << 4)) & 0x0f0f_0f0f_0f0f_0f0f;
    word = (word | (word << 2)) & 0x3333_3333_3333_3333;
    (word | (word << 1)) & 0x5555_5555_5555_5555
}

#[must_use]
pub(crate) fn square<F: BinaryField>(a: u64) -> u64 {
    debug_assert_eq!(a & !F::MASK, 0, "noncanonical field operand");
    reduce::<F>(RawProduct {
        lo: spread(a),
        hi: spread(a >> 32),
    })
}

#[must_use]
pub(crate) fn frobenius<F: BinaryField>(mut a: u64, power: u32) -> u64 {
    debug_assert_eq!(a & !F::MASK, 0, "noncanonical field operand");
    for _ in 0..power % F::BITS {
        a = square::<F>(a);
    }
    a
}
