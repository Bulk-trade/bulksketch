//! Canonical scalar maps, including even-degree quadratic solving.
#![forbid(unsafe_code)]

use crate::field::{BinaryField, gf64};

#[must_use]
pub(crate) fn trace<F: BinaryField>(a: u64) -> u8 {
    debug_assert_eq!(a & !F::MASK, 0, "noncanonical field operand");
    if F::BITS == 64 {
        // Only Z^61 and Z^63 have trace one in this polynomial basis.
        return u8::try_from(((a >> 61) ^ (a >> 63)) & 1).expect("trace is a bit");
    }
    canonical_trace::<F>(a)
}

fn canonical_trace<F: BinaryField>(a: u64) -> u8 {
    let mut sum = a;
    let mut conjugate = a;
    for _ in 1..F::BITS {
        conjugate = gf64::square::<F>(conjugate);
        sum ^= conjugate;
    }
    assert!(sum <= 1, "absolute trace must lie in GF(2)");
    u8::try_from(sum).expect("trace is a bit")
}

/// Binary Itoh-Tsujii chain for `t_k=a^(2^k-1)`, targeting `k=BITS-1`.
/// Doubling: `t_(2k)=t_k^(2^k)*t_k`; append one: `t_(k+1)=t_k^2*a`.
/// GF64 k: 1,2,3,6,7,14,15,30,31,62,63; final square gives `a^(2^64-2)`.
/// Exactly 63 squarings and 10 multiplications for nonzero, nonunit GF64 inputs.
#[must_use]
pub(crate) fn inverse<F: BinaryField>(a: u64) -> Option<u64> {
    inverse_using::<F>(a, gf64::mul::<F>, gf64::square::<F>)
}

#[inline]
pub(crate) fn inverse_using<F: BinaryField>(
    a: u64,
    mul: impl Fn(u64, u64) -> u64,
    square: impl Fn(u64) -> u64,
) -> Option<u64> {
    inverse_with_frobenius::<F>(a, mul, |mut value, power| {
        for _ in 0..power {
            value = square(value);
        }
        value
    })
}

#[inline]
pub(crate) fn inverse_with_frobenius<F: BinaryField>(
    a: u64,
    mul: impl Fn(u64, u64) -> u64,
    frobenius: impl Fn(u64, u32) -> u64,
) -> Option<u64> {
    debug_assert_eq!(a & !F::MASK, 0, "noncanonical field operand");
    if a == 0 {
        return None;
    }
    if a == 1 {
        return Some(1);
    }
    let target = F::BITS - 1;
    let mut k = 1;
    let mut t = a;
    for bit in (0..(u32::BITS - target.leading_zeros() - 1)).rev() {
        t = mul(frobenius(t, k), t);
        k *= 2;
        if target & (1 << bit) != 0 {
            t = mul(frobenius(t, 1), a);
            k += 1;
        }
    }
    Some(frobenius(t, 1))
}

/// Right inverse of Q(z)=z^2+z on trace-zero inputs, with bit zero of z fixed to zero.
/// Constants use columns 1..BITS (ascending), lowest available row first, and
/// Gauss-Jordan elimination over GF(2). Kernel(Q)={0,1}, so this fixes the only free coordinate.
#[must_use]
pub(crate) fn solve_quadratic<F: BinaryField>(a: u64) -> Option<u64> {
    if trace::<F>(a) != 0 {
        return None;
    }
    let z = quadratic_value::<F>(a);
    assert_eq!(gf64::square::<F>(z) ^ z, a, "quadratic-map invariant");
    Some(z)
}

#[inline]
pub(crate) fn quadratic_value<F: BinaryField>(a: u64) -> u64 {
    if F::BITS == 64 {
        let mut remaining = a;
        let mut value = 0;
        for table in &super::quadratic_chunks::GF64_QUADRATIC_CHUNKS {
            let index = usize::try_from(remaining & 15).expect("nibble index");
            value ^= table[index];
            remaining >>= 4;
        }
        return value;
    }
    let mut z = 0;
    for (bit, &row) in quadratic_rows::<F>().iter().enumerate() {
        z |= u64::from((row & a).count_ones() & 1) << bit;
    }
    z
}

pub(super) fn quadratic_rows<F: BinaryField>() -> &'static [u64] {
    match F::BITS {
        64 => &GF64_QUADRATIC,
        #[cfg(test)]
        2 => &GF4_QUADRATIC,
        #[cfg(test)]
        4 => &GF16_QUADRATIC,
        #[cfg(test)]
        8 => &GF256_QUADRATIC,
        #[cfg(test)]
        16 => &GF65536_QUADRATIC,
        _ => unreachable!("sealed field has no quadratic map"),
    }
}

// Regenerated from Q on the polynomial basis by the quadratic_constants test.
const GF64_QUADRATIC: [u64; 64] = [
    0x0000_0000_0000_0000,
    0x748d_c4cb_e3a9_915d,
    0x67eb_d2de_b9ce_5ace,
    0x67eb_d2de_b9ce_5ac0,
    0x135d_a537_5f37_f7e8,
    0x135d_a537_5f37_f7de,
    0x235e_1ebf_1e67_6bde,
    0x2365_ad9d_1b37_577e,
    0x2353_9353_1d5d_7ee8,
    0x136b_9bf9_595d_ddfe,
    0x2e52_b4ad_2c63_2d37,
    0x2e64_8a63_2a09_0917,
    0x2385_11e1_1359_4db7,
    0x2ebf_853d_2737_177e,
    0x3dd9_93fe_7d5e_be69,
    0x3003_bb5e_415e_1e69,
    0x2353_938b_1d50_7ce8,
    0x3003_bb86_4150_9c69,
    0x0d3a_94e4_346e_6a80,
    0x2e52_b49b_2c6d_2b17,
    0x2ebf_865d_273f_377e,
    0x2ebf_866b_2709_315e,
    0x30d8_ba38_4c04_a200,
    0x3003_b630_41e4_9a49,
    0x0368_f644_19ea_58c9,
    0x10ee_5195_48d7_8f37,
    0x0e89_5890_25c4_3a49,
    0x30d8_8c38_4424_a200,
    0x1d37_2105_6713_b57e,
    0x1036_3ec3_6669_a917,
    0x3000_0000_0000_0000,
    0x1035_859d_c737_b77e,
    0x2000_0000_0000_0001,
    0x1366_1615_5a67_cb97,
    0x003b_b322_0550_3c69,
    0x235e_1ebf_1e67_6b97,
    0x3035_8546_473a_b469,
    0x1e51_0f25_6d33_b57e,
    0x30ee_8a18_4a04_8200,
    0x00ed_3146_0b5a_1c69,
    0x30ee_8ac0_4a08_8000,
    0x1ebc_3e5b_666d_ab17,
    0x3003_b830_4144_9a49,
    0x0000_0e00_0020_0000,
    0x10ee_5f95_4af7_8f37,
    0x2036_d3ad_06d3_2d37,
    0x3000_ed6e_40ba_8420,
    0x2035_68f3_078d_335e,
    0x3353_7ee4_5dea_f8c9,
    0x100d_6053_438d_935e,
    0x0e5c_6f56_2ebe_2620,
    0x0eb1_5e90_25e4_3a49,
    0x100d_62cb_4389_915e,
    0x100d_64cb_43a9_915e,
    0x303b_9766_457a_bc69,
    0x100e_7f95_42f7_8f37,
    0x0001_1fc6_017a_1c69,
    0x0eb8_4156_249e_2620,
    0x1e95_259d_6737_b77e,
    0x0e1b_5a08_25c0_3849,
    0x02a3_1b5e_015e_1e69,
    0x04b8_4156_249e_2620,
    0x2000_0000_0000_0000,
    0x748d_c4cb_e3a9_915e,
];
#[cfg(test)]
const GF4_QUADRATIC: [u64; 2] = [0x0000_0000_0000_0000, 0x0000_0000_0000_0001];
#[cfg(test)]
const GF16_QUADRATIC: [u64; 4] = [
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0003,
    0x0000_0000_0000_0001,
    0x0000_0000_0000_0006,
];
#[cfg(test)]
const GF256_QUADRATIC: [u64; 8] = [
    0x0000_0000_0000_0000,
    0x0000_0000_0000_006a,
    0x0000_0000_0000_0079,
    0x0000_0000_0000_0077,
    0x0000_0000_0000_0021,
    0x0000_0000_0000_0017,
    0x0000_0000_0000_0020,
    0x0000_0000_0000_0069,
];
#[cfg(test)]
const GF65536_QUADRATIC: [u64; 16] = [
    0x0000_0000_0000_0000,
    0x0000_0000_0000_0315,
    0x0000_0000_0000_184f,
    0x0000_0000_0000_1841,
    0x0000_0000_0000_72df,
    0x0000_0000_0000_71fe,
    0x0000_0000_0000_0a49,
    0x0000_0000_0000_7b5e,
    0x0000_0000_0000_6997,
    0x0000_0000_0000_0a00,
    0x0000_0000_0000_73de,
    0x0000_0000_0000_1468,
    0x0000_0000_0000_3a48,
    0x0000_0000_0000_0536,
    0x0000_0000_0000_2000,
    0x0000_0000_0000_0316,
];
