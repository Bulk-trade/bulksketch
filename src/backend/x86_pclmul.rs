//! Scalar XMM kernels; only checked dispatch and feature-checked tests reach this module.
#![allow(unsafe_code)]

#[cfg(test)]
use std::arch::x86_64::_mm_setzero_si128;
use {
    super::contract::{Arithmetic, BulkKernels},
    crate::{
        field::{BinaryField, gf64, maps},
        types::RawProduct,
    },
    std::arch::x86_64::{
        __m128i, _mm_clmulepi64_si128, _mm_cvtsi64_si128, _mm_cvtsi128_si64, _mm_srli_si128,
        _mm_xor_si128,
    },
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct Pclmul;

#[cfg(test)]
pub(super) fn reduce_cl_for_test(product: RawProduct) -> u64 {
    assert!(std::is_x86_feature_detected!("pclmulqdq"));
    // SAFETY: detection above checks PCLMUL; the other intrinsics need baseline SSE2.
    unsafe {
        let value = std::arch::x86_64::_mm_set_epi64x(
            i64::from_ne_bytes(product.hi.to_ne_bytes()),
            i64::from_ne_bytes(product.lo.to_ne_bytes()),
        );
        low(reduced::<crate::field::Gf64, true>(value))
    }
}

impl<F: BinaryField> Arithmetic<F> for Pclmul {
    fn mul(a: u64, b: u64) -> u64 {
        // SAFETY: Pclmul is selected only after runtime PCLMUL detection.
        unsafe { multiply::<F, true>(a, b) }
    }

    fn square(a: u64) -> u64 {
        // SAFETY: checked dispatch guarantees PCLMUL; SSE2 is architectural on x86-64.
        unsafe { multiply::<F, true>(a, a) }
    }

    fn frobenius(a: u64, power: u32) -> u64 {
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { frobenius::<F>(a, power) }
    }

    fn inverse(a: u64) -> Option<u64> {
        #[cfg(test)]
        super::test_observer::inverse();
        #[cfg(test)]
        crate::types::small_degree_observer::inverse();
        // SAFETY: checked dispatch detects PCLMULQDQ before selecting this backend.
        unsafe { inverse::<F>(a) }
    }

    fn trace(a: u64) -> u8 {
        maps::trace::<F>(a)
    }

    fn solve_quadratic(a: u64) -> Option<u64> {
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { solve_quadratic::<F>(a) }
    }

    fn raw_mul(a: u64, b: u64) -> RawProduct {
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { raw_product(a, b) }
    }

    fn reduce(product: RawProduct) -> u64 {
        gf64::reduce::<F>(product)
    }

    #[cfg(test)]
    fn dot(a: &[u64], b: &[u64]) -> u64 {
        assert_eq!(a.len(), b.len(), "dot length mismatch");
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { dot::<F, false>(a, b) }
    }

    fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64) {
        assert_eq!(dst.len(), src.len(), "scale_xor length mismatch");
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { scale_xor::<F, true>(dst, src, scale) }
    }

    fn square_slice(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len(), "square_slice length mismatch");
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { square_slice::<F, true>(dst, src) }
    }
}

impl<F: BinaryField> BulkKernels<F> for Pclmul {
    fn insert_nonzero(odd: &mut [u64], ids: &[u64]) {
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { insert::<F, true>(odd, ids) }
    }

    fn xor_assign(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len(), "xor_assign length mismatch");
        for (target, &source) in dst.iter_mut().zip(src) {
            *target ^= source;
        }
    }

    fn horner_many(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
        assert_eq!(out.len(), points.len(), "horner_many length mismatch");
        // SAFETY: this backend is reachable only through checked dispatch.
        unsafe { horner::<F, true>(coefficients, points, out) }
    }
}

#[inline]
fn word(a: u64) -> __m128i {
    // SAFETY: SSE2 is part of the x86-64 baseline, with no memory operands here.
    unsafe { _mm_cvtsi64_si128(i64::from_ne_bytes(a.to_ne_bytes())) }
}

#[inline]
fn low(product: __m128i) -> u64 {
    // SAFETY: SSE2 is part of the x86-64 baseline, with no memory operands here.
    u64::from_ne_bytes(unsafe { _mm_cvtsi128_si64(product) }.to_ne_bytes())
}

#[inline]
fn words(product: __m128i) -> RawProduct {
    // SAFETY: SSE2 is architectural on x86-64; the shift stays within this register.
    let high = unsafe { _mm_srli_si128::<8>(product) };
    RawProduct {
        lo: low(product),
        hi: low(high),
    }
}

#[inline]
#[target_feature(enable = "pclmulqdq")]
unsafe fn raw_product(a: u64, b: u64) -> RawProduct {
    words(_mm_clmulepi64_si128::<0x00>(word(a), word(b)))
}

#[inline]
#[target_feature(enable = "pclmulqdq")]
unsafe fn reduced<F: BinaryField, const CL: bool>(product: __m128i) -> __m128i {
    if CL && F::BITS == 64 {
        let modulus = word(F::MODULUS_LOW);
        let first = _mm_clmulepi64_si128::<0x01>(product, modulus);
        let second = _mm_clmulepi64_si128::<0x01>(first, modulus);
        _mm_xor_si128(_mm_xor_si128(product, first), second)
    } else {
        word(gf64::reduce::<F>(words(product)))
    }
}

#[inline]
#[target_feature(enable = "pclmulqdq")]
unsafe fn multiply<F: BinaryField, const CL: bool>(a: u64, b: u64) -> u64 {
    let product = _mm_clmulepi64_si128::<0x00>(word(a), word(b));
    // SAFETY: the enclosing function has the same PCLMUL feature requirement.
    low(unsafe { reduced::<F, CL>(product) })
}

#[cfg(test)]
#[target_feature(enable = "pclmulqdq")]
unsafe fn dot<F: BinaryField, const CL: bool>(a: &[u64], b: &[u64]) -> u64 {
    let mut sum = _mm_setzero_si128();
    for (&left, &right) in a.iter().zip(b) {
        sum = _mm_xor_si128(sum, _mm_clmulepi64_si128::<0x00>(word(left), word(right)));
    }
    // SAFETY: the enclosing function has the same PCLMUL feature requirement.
    low(unsafe { reduced::<F, CL>(sum) })
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn scale_xor<F: BinaryField, const CL: bool>(dst: &mut [u64], src: &[u64], scale: u64) {
    if scale == 0 {
        return;
    }
    if scale == 1 {
        for (target, &source) in dst.iter_mut().zip(src) {
            *target ^= source;
        }
        return;
    }
    let scale = word(scale);
    for (target, &source) in dst.iter_mut().zip(src) {
        let product = _mm_clmulepi64_si128::<0x00>(word(source), scale);
        // SAFETY: the enclosing function has the same PCLMUL feature requirement.
        *target ^= low(unsafe { reduced::<F, CL>(product) });
    }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn square_slice<F: BinaryField, const CL: bool>(dst: &mut [u64], src: &[u64]) {
    for (target, &source) in dst.iter_mut().zip(src) {
        let source = word(source);
        let product = _mm_clmulepi64_si128::<0x00>(source, source);
        // SAFETY: the enclosing function has the same PCLMUL feature requirement.
        *target = low(unsafe { reduced::<F, CL>(product) });
    }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn insert<F: BinaryField, const CL: bool>(odd: &mut [u64], ids: &[u64]) {
    let Some((first, successors)) = odd.split_first_mut() else {
        return;
    };
    for &id in ids {
        *first ^= id;
        // SAFETY: the enclosing function has the same PCLMUL feature requirement.
        let square = word(unsafe { multiply::<F, false>(id, id) });
        let mut power = word(id);
        for syndrome in &mut *successors {
            let product = _mm_clmulepi64_si128::<0x00>(power, square);
            // SAFETY: the enclosing function has the same PCLMUL feature requirement.
            power = unsafe { reduced::<F, CL>(product) };
            *syndrome ^= low(power);
        }
    }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn horner<F: BinaryField, const CL: bool>(
    coefficients: &[u64],
    points: &[u64],
    out: &mut [u64],
) {
    let Some((&leading, rest)) = coefficients.split_last() else {
        out.fill(0);
        return;
    };
    for (target, &point) in out.iter_mut().zip(points) {
        let point = word(point);
        let mut value = word(leading);
        for &coefficient in rest.iter().rev() {
            let product = _mm_clmulepi64_si128::<0x00>(value, point);
            // SAFETY: the enclosing function has the same PCLMUL feature requirement.
            value = _mm_xor_si128(unsafe { reduced::<F, CL>(product) }, word(coefficient));
        }
        *target = low(value);
    }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn frobenius<F: BinaryField>(mut a: u64, power: u32) -> u64 {
    if F::BITS == 64
        && let Some(value) = crate::field::frobenius::lookup(a, power % F::BITS)
    {
        return value;
    }
    for _ in 0..power % F::BITS {
        // SAFETY: the enclosing function has the same PCLMUL feature requirement.
        a = unsafe { multiply::<F, false>(a, a) };
    }
    a
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn inverse<F: BinaryField>(a: u64) -> Option<u64> {
    if F::BITS != 64 {
        return maps::inverse_with_frobenius::<F>(
            a,
            // SAFETY: the enclosing function requires PCLMULQDQ.
            |left, right| unsafe { multiply::<F, true>(left, right) },
            // SAFETY: the enclosing function requires PCLMULQDQ.
            |value, power| unsafe { frobenius::<F>(value, power) },
        );
    }
    if a == 0 {
        return None;
    }
    if a == 1 {
        return Some(1);
    }
    // t_k = a^(2^k - 1). The chain 1,2,3,6,7,14,21,42,63 uses
    // eight products; fixed linear maps replace the long Frobenius runs.
    let map7 = |value| crate::field::frobenius::lookup(value, 7).expect("fixed inverse map");
    let map21 = crate::field::frobenius::inverse21;
    // SAFETY: every multiply below requires the enclosing PCLMULQDQ feature.
    unsafe {
        let t2 = multiply::<F, true>(multiply::<F, false>(a, a), a);
        let t3 = multiply::<F, true>(multiply::<F, false>(t2, t2), a);
        let f3 = crate::field::frobenius::lookup(t3, 3).expect("fixed inverse map");
        let t6 = multiply::<F, true>(f3, t3);
        let t7 = multiply::<F, true>(multiply::<F, false>(t6, t6), a);
        let t14 = multiply::<F, true>(map7(t7), t7);
        let t21 = multiply::<F, true>(map7(t14), t7);
        let t42 = multiply::<F, true>(map21(t21), t21);
        let t63 = multiply::<F, true>(map21(t42), t21);
        Some(multiply::<F, false>(t63, t63))
    }
}

#[target_feature(enable = "pclmulqdq")]
unsafe fn solve_quadratic<F: BinaryField>(a: u64) -> Option<u64> {
    if maps::trace::<F>(a) != 0 {
        return None;
    }
    let solution = maps::quadratic_value::<F>(a);
    // SAFETY: the enclosing function has the same PCLMUL feature requirement.
    let square = unsafe { multiply::<F, false>(solution, solution) };
    assert_eq!(square ^ solution, a, "quadratic-map invariant");
    Some(solution)
}
