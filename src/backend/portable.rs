//! Safe canonical-word kernels shared by GF64 and the sealed test fields.
#![forbid(unsafe_code)]

use crate::{
    backend::contract::{Arithmetic, BulkKernels},
    field::{BinaryField, gf64, maps},
    types::RawProduct,
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Portable;

impl<F: BinaryField> Arithmetic<F> for Portable {
    fn mul(a: u64, b: u64) -> u64 {
        gf64::mul::<F>(a, b)
    }

    fn square(a: u64) -> u64 {
        gf64::square::<F>(a)
    }

    fn frobenius(a: u64, power: u32) -> u64 {
        gf64::frobenius::<F>(a, power)
    }

    fn inverse(a: u64) -> Option<u64> {
        #[cfg(test)]
        super::test_observer::inverse();
        #[cfg(test)]
        crate::types::small_degree_observer::inverse();
        maps::inverse::<F>(a)
    }

    fn trace(a: u64) -> u8 {
        maps::trace::<F>(a)
    }

    fn solve_quadratic(a: u64) -> Option<u64> {
        maps::solve_quadratic::<F>(a)
    }

    fn raw_mul(a: u64, b: u64) -> RawProduct {
        gf64::raw_mul::<F>(a, b)
    }

    fn reduce(product: RawProduct) -> u64 {
        gf64::reduce::<F>(product)
    }

    #[cfg(test)]
    fn dot(a: &[u64], b: &[u64]) -> u64 {
        assert_eq!(a.len(), b.len(), "dot length mismatch");
        let mut sum = RawProduct::default();
        for (&left, &right) in a.iter().zip(b) {
            let product = <Self as Arithmetic<F>>::raw_mul(left, right);
            sum.lo ^= product.lo;
            sum.hi ^= product.hi;
        }
        <Self as Arithmetic<F>>::reduce(sum)
    }

    fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64) {
        assert_eq!(dst.len(), src.len(), "scale_xor length mismatch");
        if scale == 0 {
            return;
        }
        if scale == 1 {
            <Self as BulkKernels<F>>::xor_assign(dst, src);
            return;
        }
        for (target, &source) in dst.iter_mut().zip(src) {
            *target ^= <Self as Arithmetic<F>>::mul(source, scale);
        }
    }

    fn square_slice(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len(), "square_slice length mismatch");
        for (target, &source) in dst.iter_mut().zip(src) {
            *target = <Self as Arithmetic<F>>::square(source);
        }
    }
}

impl<F: BinaryField> BulkKernels<F> for Portable {
    fn insert_nonzero(odd: &mut [u64], ids: &[u64]) {
        let Some((first, successors)) = odd.split_first_mut() else {
            return;
        };
        // Zero extraction and canonicality belong to the caller, as does routing.
        for &id in ids {
            *first ^= id;
            let square = <Self as Arithmetic<F>>::square(id);
            let mut power = id;
            // Advancing before each successor uses exactly c-1 multiplications.
            for syndrome in &mut *successors {
                power = <Self as Arithmetic<F>>::mul(power, square);
                *syndrome ^= power;
            }
        }
    }

    fn xor_assign(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len(), "xor_assign length mismatch");
        for (target, &source) in dst.iter_mut().zip(src) {
            *target ^= source;
        }
    }

    fn horner_many(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
        assert_eq!(out.len(), points.len(), "horner_many length mismatch");
        let Some((&leading, rest)) = coefficients.split_last() else {
            out.fill(0);
            return;
        };
        for (target, &point) in out.iter_mut().zip(points) {
            *target = rest.iter().rev().fold(leading, |value, &coefficient| {
                <Self as Arithmetic<F>>::mul(value, point) ^ coefficient
            });
        }
    }
}
