//! Each backend implements these static, monomorphized contracts for each checked capability.
#![forbid(unsafe_code)]

use crate::{field::BinaryField, types::RawProduct};

/// All operands/results are canonical F words. Slice dimensions are internal invariants.
/// Inverse rejects zero; raw products are unreduced polynomials, never field elements.
pub(crate) trait Arithmetic<F: BinaryField>: Copy + Send + Sync + 'static {
    fn mul(a: u64, b: u64) -> u64;
    fn square(a: u64) -> u64;
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "arithmetic parity contract; insertion uses fixed private maps"
        )
    )]
    fn frobenius(a: u64, power: u32) -> u64;
    fn inverse(a: u64) -> Option<u64>;
    /// Absolute field trace, 0 or 1. Canonical scalar maps live in the field module.
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "arithmetic parity contract; scalar map owns current trace callers"
        )
    )]
    fn trace(a: u64) -> u8;
    /// Deterministic right inverse of z^2+z on trace-zero inputs; verify each solution.
    /// Even-degree fields use the fixed-pivot map, never the odd-degree half trace.
    fn solve_quadratic(a: u64) -> Option<u64>;
    fn raw_mul(a: u64, b: u64) -> RawProduct;
    fn reduce(product: RawProduct) -> u64;
    /// Equal lengths; XOR raw products then reduce once, including the empty dot = 0.
    #[cfg(test)]
    fn dot(a: &[u64], b: &[u64]) -> u64;
    /// Equal lengths; dst[i] ^= src[i] * scale. Aliasing follows safe Rust borrows.
    fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64);
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "bulk parity contract; current reconstruction squares dependent positions"
        )
    )]
    fn square_slice(dst: &mut [u64], src: &[u64]);
}

/// Bulk arithmetic, without shape, wire, request, job or complete-operation types.
pub(crate) trait BulkKernels<F: BinaryField>: Arithmetic<F> {
    /// Optional monic square-mod kernel; false leaves both mutable slices untouched.
    /// Degree d>=3, a.len<=d, table.len=d*floor(d/2), dst.len=d, raw.len>=2*d+1.
    fn square_mod(_a: &[u64], _table: &[u64], _dst: &mut [u64], _raw: &mut [RawProduct]) -> bool {
        false
    }

    /// Multiply an ascending polynomial in place by (1 + root*z). Its final
    /// coefficient must initially be zero; the slice includes that spare word.
    fn multiply_linear(coefficients: &mut [u64], root: u64) {
        for index in (1..coefficients.len()).rev() {
            coefficients[index] ^= Self::mul(coefficients[index - 1], root);
        }
    }

    /// Check all odd-sequence continuation equations, after the caller has
    /// independently verified its first d words. squared_locator is rebuilt
    /// from roots, has d+1 ascending words and constant coefficient one.
    fn odd_recurrence_matches(odd: &[u64], squared_locator: &[u64]) -> bool {
        let degree = squared_locator.len() - 1;
        for index in degree..odd.len() {
            let mut sum = RawProduct::default();
            for lag in 1..=degree {
                let product = Self::raw_mul(odd[index - lag], squared_locator[lag]);
                sum.lo ^= product.lo;
                sum.hi ^= product.hi;
            }
            if Self::reduce(sum) != odd[index] {
                return false;
            }
        }
        true
    }

    /// Toggle nonzero canonical IDs into S1,S3,... in arrival order. Parity semantics.
    /// Caller handles routing/zero and validates every input. No post-final multiply.
    fn insert_nonzero(odd: &mut [u64], ids: &[u64]);
    /// Overwrite all odd syndromes with the direct encoding of these IDs.
    fn encode_nonzero(odd: &mut [u64], ids: &[u64]) {
        odd.fill(0);
        if ids.len() <= 2 {
            for id in ids {
                Self::insert_nonzero(odd, std::slice::from_ref(id));
            }
        } else {
            Self::insert_nonzero(odd, ids);
        }
    }

    /// Equal lengths; XOR algebraic words only, never wire metadata.
    fn xor_assign(dst: &mut [u64], src: &[u64]);
    /// XOR canonical local words with unaligned little-endian remote words.
    /// Equal word lengths; returns whether any output word is nonzero.
    fn difference(dst: &mut [u64], local: &[u64], remote: &[u8]) -> bool {
        #[cfg(test)]
        super::test_observer::difference();
        assert_eq!(dst.len(), local.len(), "difference length mismatch");
        assert_eq!(
            remote.len(),
            8 * dst.len(),
            "difference byte length mismatch"
        );
        let mut any = 0;
        for ((out, &word), bytes) in dst.iter_mut().zip(local).zip(remote.chunks_exact(8)) {
            *out = word ^ u64::from_le_bytes(bytes.try_into().expect("complete word"));
            any |= *out;
        }
        any != 0
    }
    /// Ascending coefficients; empty polynomial evaluates to zero. out.len=points.len.
    fn horner_many(coefficients: &[u64], points: &[u64], out: &mut [u64]);
}
