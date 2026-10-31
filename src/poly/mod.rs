//! Private dense-polynomial contract. No general polynomial package is exported.
#![forbid(unsafe_code)]

use crate::{backend::contract::BulkKernels, field::BinaryField, types::RawProduct};

mod dense;

/// The row decoder monomorphizes this marker with its field and backend.
/// gcd(0,0) is zero. Failed exact division clears q[..a.len()+1] and leaves
/// the canonical remainder in rem, zero-padded through a.len()+1.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Dense;

#[cfg(test)]
mod dense_tests;
#[cfg(test)]
mod kernel_count_tests;
#[cfg(test)]
mod square_mod_tests;

/// Canonical ascending slices: empty is zero; nonempty has no trailing zero.
/// Output slices are caller-owned, sufficiently sized, and return their normalized length.
/// Input/output aliasing follows Rust borrows. Zero divisors violate internal invariants.
/// The row driver charges `WorkScheduleV1` *before* invoking these unmetered kernels.
#[cfg_attr(
    not(test),
    expect(
        dead_code,
        reason = "test polynomial oracles consume the remaining private primitives"
    )
)]
pub(crate) trait Polynomial<F: BinaryField, K: BulkKernels<F>> {
    /// dst and raw each have at least a.len+b.len words (zero inputs need zero words).
    fn mul_into(a: &[u64], b: &[u64], dst: &mut [u64], raw: &mut [RawProduct]) -> usize;
    /// dst/raw each have at least 2*a.len words.
    fn square_into(a: &[u64], dst: &mut [u64], raw: &mut [RawProduct]) -> usize;
    /// q, rem and raw each have at least a.len+1 words. Returns `(q_len, rem_len)`.
    fn div_rem_into(
        a: &[u64],
        b: &[u64],
        q: &mut [u64],
        rem: &mut [u64],
        raw: &mut [RawProduct],
    ) -> (usize, usize);
    /// Same storage as `div_rem_into`; None if remainder is nonzero. No provisional q is published.
    fn exact_divide_into(
        a: &[u64],
        b: &[u64],
        q: &mut [u64],
        rem: &mut [u64],
        raw: &mut [RawProduct],
    ) -> Option<usize>;
    /// dst has max(a.len,b.len) words; work has `4*(max_len+1)`, raw has `2*(max_len+1)`.
    fn monic_gcd_into(
        a: &[u64],
        b: &[u64],
        dst: &mut [u64],
        work: &mut [u64],
        raw: &mut [RawProduct],
    ) -> usize;
    fn eval_many_into(coefficients: &[u64], points: &[u64], out: &mut [u64]);
    /// Extend with zeros through index, XOR value, normalize. dst has index+1 capacity.
    fn xor_coefficient(dst: &mut [u64], len: usize, index: usize, value: u64) -> usize;
    /// Monic degree d>=3; table needs d*floor(d/2), work needs 4*(d+1) words.
    fn prepare_square_table(modulus: &[u64], table: &mut [u64], work: &mut [u64]);
    /// dst has d words; raw has 2*d+1; table is the exact table for this modulus.
    fn square_mod_into(
        a: &[u64],
        modulus: &[u64],
        table: &[u64],
        dst: &mut [u64],
        raw: &mut [RawProduct],
    ) -> usize;
}
