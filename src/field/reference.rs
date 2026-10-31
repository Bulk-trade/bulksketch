//! Independent bit-serial oracle; no portable folding or squaring code is reused.
#![forbid(unsafe_code)]

use crate::{field::BinaryField, types::RawProduct};

#[expect(
    clippy::cast_possible_truncation,
    reason = "split a polynomial into its low and high words"
)]
pub(crate) fn raw_mul<F: BinaryField>(a: u64, b: u64) -> RawProduct {
    assert_eq!((a | b) & !F::MASK, 0, "noncanonical oracle operand");
    let mut product = 0_u128;
    for bit in 0..F::BITS {
        if b & (1_u64 << bit) != 0 {
            product ^= u128::from(a) << bit;
        }
    }
    RawProduct {
        lo: product as u64,
        hi: (product >> 64) as u64,
    }
}

pub(crate) fn reduce<F: BinaryField>(product: RawProduct) -> u64 {
    let mut polynomial = (u128::from(product.hi) << 64) | u128::from(product.lo);
    let modulus = (1_u128 << F::BITS) | u128::from(F::MODULUS_LOW);
    for bit in (F::BITS..128).rev() {
        if polynomial & (1_u128 << bit) != 0 {
            polynomial ^= modulus << (bit - F::BITS);
        }
    }
    u64::try_from(polynomial).expect("remainder degree is below the field degree")
}

pub(crate) fn mul<F: BinaryField>(a: u64, b: u64) -> u64 {
    reduce::<F>(raw_mul::<F>(a, b))
}
