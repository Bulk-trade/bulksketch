//! Eight compact GF64 lanes, with four products per VPCLMUL instruction.
#![allow(unsafe_code)]

use {
    super::{
        contract::{Arithmetic, BulkKernels},
        portable::Portable,
        x86_pclmul::Pclmul,
    },
    crate::{
        field::{BinaryField, frobenius::square as map_square},
        types::RawProduct,
    },
    core::arch::x86_64::{
        __cpuid, __cpuid_count, __m512i, _mm_cvtsi128_si64, _mm512_castsi512_si128,
        _mm512_clmulepi64_epi128, _mm512_mask_mov_epi64, _mm512_mask_storeu_epi64,
        _mm512_maskz_loadu_epi64, _mm512_or_si512, _mm512_permutex2var_epi64,
        _mm512_permutexvar_epi64, _mm512_set_epi64, _mm512_set1_epi64, _mm512_setzero_si512,
        _mm512_shuffle_epi32, _mm512_shuffle_i64x2, _mm512_slli_epi64, _mm512_srli_epi64,
        _mm512_test_epi64_mask, _mm512_unpackhi_epi64, _mm512_unpacklo_epi64, _mm512_xor_si512,
        _xgetbv,
    },
};

type ScalarArithmetic = Pclmul;

#[derive(Clone, Copy, Debug)]
pub(crate) struct Vpclmul512;

#[inline]
pub(super) fn available() -> bool {
    static AVAILABLE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *AVAILABLE.get_or_init(detect)
}

fn detect() -> bool {
    // SAFETY: CPUID is architectural on x86-64. XGETBV is reached only when
    // CPUID reports both XSAVE and OSXSAVE; no vector instruction executes here.
    unsafe {
        let leaf1 = __cpuid(1);
        let leaf7 = __cpuid_count(7, 0);
        let cpu = leaf7.ebx & (1 << 16) != 0 && leaf7.ecx & (1 << 10) != 0;
        let xsave = leaf1.ecx & (3 << 26) == 3 << 26;
        let os = xsave && _xgetbv(0) & 0xe6 == 0xe6;
        super::detect::vpclmul512_supported(cpu, os)
    }
}

impl<F: BinaryField> Arithmetic<F> for Vpclmul512 {
    fn mul(a: u64, b: u64) -> u64 {
        <ScalarArithmetic as Arithmetic<F>>::mul(a, b)
    }
    fn square(a: u64) -> u64 {
        <ScalarArithmetic as Arithmetic<F>>::square(a)
    }
    fn frobenius(a: u64, power: u32) -> u64 {
        <ScalarArithmetic as Arithmetic<F>>::frobenius(a, power)
    }
    fn inverse(a: u64) -> Option<u64> {
        <ScalarArithmetic as Arithmetic<F>>::inverse(a)
    }
    fn trace(a: u64) -> u8 {
        <ScalarArithmetic as Arithmetic<F>>::trace(a)
    }
    fn solve_quadratic(a: u64) -> Option<u64> {
        <ScalarArithmetic as Arithmetic<F>>::solve_quadratic(a)
    }
    fn raw_mul(a: u64, b: u64) -> RawProduct {
        <ScalarArithmetic as Arithmetic<F>>::raw_mul(a, b)
    }
    fn reduce(p: RawProduct) -> u64 {
        <ScalarArithmetic as Arithmetic<F>>::reduce(p)
    }

    #[cfg(test)]
    fn dot(a: &[u64], b: &[u64]) -> u64 {
        assert_eq!(a.len(), b.len(), "dot length mismatch");
        if F::BITS != 64 {
            return <Portable as Arithmetic<F>>::dot(a, b);
        }
        // SAFETY: dispatch selects this backend only after available(); all loads
        // are masked to the admitted slices. Test callers use the same gate.
        unsafe { dot(a, b) }
    }

    fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64) {
        assert_eq!(dst.len(), src.len(), "scale_xor length mismatch");
        if F::BITS != 64 {
            return <Portable as Arithmetic<F>>::scale_xor(dst, src, scale);
        }
        // SAFETY: checked backend selection guarantees both target features.
        unsafe { scale_xor(dst, src, scale) }
    }

    fn square_slice(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len(), "square_slice length mismatch");
        if F::BITS != 64 {
            return <Portable as Arithmetic<F>>::square_slice(dst, src);
        }
        // SAFETY: checked backend selection guarantees both target features.
        unsafe { square_slice(dst, src) }
    }
}

impl<F: BinaryField> BulkKernels<F> for Vpclmul512 {
    fn square_mod(a: &[u64], table: &[u64], dst: &mut [u64], raw: &mut [RawProduct]) -> bool {
        if F::BITS != 64 {
            return false;
        }
        // SAFETY: backend selection checked AVX-512F, VPCLMULQDQ and OS ZMM state.
        // Dense::square_mod_into checks the slice dimensions before this call.
        unsafe { square_mod(a, table, dst, raw) }
        true
    }

    fn multiply_linear(coefficients: &mut [u64], root: u64) {
        if F::BITS != 64 {
            return <Portable as BulkKernels<F>>::multiply_linear(coefficients, root);
        }
        // SAFETY: checked backend selection guarantees both target features.
        unsafe { multiply_linear(coefficients, root) }
    }

    fn odd_recurrence_matches(odd: &[u64], squared_locator: &[u64]) -> bool {
        if F::BITS != 64 {
            return <Portable as BulkKernels<F>>::odd_recurrence_matches(odd, squared_locator);
        }
        // SAFETY: checked backend selection guarantees both target features;
        // every masked load is bounded by the admitted input slices.
        unsafe { odd_recurrence_matches(odd, squared_locator) }
    }

    fn insert_nonzero(odd: &mut [u64], ids: &[u64]) {
        if odd.is_empty() || ids.is_empty() {
            return;
        }
        if F::BITS != 64 {
            return <Portable as BulkKernels<F>>::insert_nonzero(odd, ids);
        }
        // SAFETY: checked backend selection guarantees both target features.
        unsafe { insert(odd, ids) }
    }

    fn encode_nonzero(odd: &mut [u64], ids: &[u64]) {
        if F::BITS == 64 && odd.len() == 18 && matches!(ids.len(), 1 | 2) {
            // SAFETY: checked backend selection guarantees AVX-512F and VPCLMULQDQ.
            unsafe { encode_18(odd, ids) }
            return;
        }
        odd.fill(0);
        if ids.len() <= 2 {
            for id in ids {
                <Self as BulkKernels<F>>::insert_nonzero(odd, std::slice::from_ref(id));
            }
        } else {
            <Self as BulkKernels<F>>::insert_nonzero(odd, ids);
        }
    }

    fn xor_assign(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len(), "xor_assign length mismatch");
        // SAFETY: checked backend selection guarantees AVX-512 state.
        unsafe { xor_assign(dst, src) }
    }

    fn difference(dst: &mut [u64], local: &[u64], remote: &[u8]) -> bool {
        #[cfg(test)]
        super::test_observer::difference();
        assert_eq!(dst.len(), local.len(), "difference length mismatch");
        assert_eq!(
            remote.len(),
            8 * dst.len(),
            "difference byte length mismatch"
        );
        // SAFETY: this backend is constructed only after CPU/OS-state checks.
        // The kernel masks every load/store to the equal admitted slice lengths.
        unsafe { difference(dst, local, remote) }
    }

    fn horner_many(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
        assert_eq!(out.len(), points.len(), "horner_many length mismatch");
        if F::BITS != 64 {
            return <Portable as BulkKernels<F>>::horner_many(coefficients, points, out);
        }
        // SAFETY: checked backend selection guarantees both target features.
        unsafe { horner_many(coefficients, points, out) }
    }
}

fn mask(len: usize) -> u8 {
    debug_assert!(len <= 8);
    if len == 0 { 0 } else { u8::MAX >> (8 - len) }
}

#[target_feature(enable = "avx512f")]
fn load(words: &[u64]) -> __m512i {
    // SAFETY: only the low words.len() lanes are accessed, and unaligned
    // addresses are permitted. Every caller supplies at most eight words.
    unsafe { _mm512_maskz_loadu_epi64(mask(words.len()), words.as_ptr().cast()) }
}

#[target_feature(enable = "avx512f")]
fn store(words: &mut [u64], value: __m512i) {
    // SAFETY: the mask limits writes to this exclusively borrowed slice.
    unsafe { _mm512_mask_storeu_epi64(words.as_mut_ptr().cast(), mask(words.len()), value) }
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn raw(a: __m512i, b: __m512i) -> (__m512i, __m512i) {
    (
        _mm512_clmulepi64_epi128::<0x00>(a, b),
        _mm512_clmulepi64_epi128::<0x11>(a, b),
    )
}

// Eight output coefficients of the current, already charged row per vector.
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn square_mod(a: &[u64], table: &[u64], dst: &mut [u64], scratch: &mut [RawProduct]) {
    let degree = dst.len();
    let first_high = degree.div_ceil(2);
    dst.fill(0);
    for (i, &coefficient) in a.iter().enumerate() {
        let square = <ScalarArithmetic as Arithmetic<crate::field::Gf64>>::square(coefficient);
        scratch[i].lo = square;
        if i < first_high {
            dst[2 * i] = square;
        }
    }
    // Reuse the raw scratch for coefficient squares. Each table row scales a
    // contiguous output block; XOR unreduced products across all high inputs
    // and reduce just once per block. Masked loads/stores handle the last block.
    for offset in (0..degree).step_by(8) {
        let end = (offset + 8).min(degree);
        let mut even = _mm512_setzero_si512();
        let mut odd = even;
        for (i, square) in scratch[..a.len()].iter().enumerate().skip(first_high) {
            let start = (i - first_high) * degree;
            let scale = _mm512_set1_epi64(i64::from_ne_bytes(square.lo.to_ne_bytes()));
            let (lo, hi) = raw(scale, load(&table[start + offset..start + end]));
            even = _mm512_xor_si512(even, lo);
            odd = _mm512_xor_si512(odd, hi);
        }
        let result = reduce_shift(
            _mm512_unpacklo_epi64(even, odd),
            _mm512_unpackhi_epi64(even, odd),
        );
        let out = &mut dst[offset..end];
        store(out, _mm512_xor_si512(load(out), result));
    }
}

#[target_feature(enable = "avx512f")]
fn horizontal_xor(mut value: __m512i) -> u64 {
    value = _mm512_xor_si512(value, _mm512_shuffle_i64x2::<0x4e>(value, value));
    value = _mm512_xor_si512(value, _mm512_shuffle_i64x2::<0xb1>(value, value));
    value = _mm512_xor_si512(value, _mm512_shuffle_epi32::<0x4e>(value));
    u64::from_ne_bytes(_mm_cvtsi128_si64(_mm512_castsi512_si128(value)).to_ne_bytes())
}

#[target_feature(enable = "avx512f")]
fn reduce_shift(lo: __m512i, hi: __m512i) -> __m512i {
    let overflow = _mm512_xor_si512(
        _mm512_srli_epi64::<63>(hi),
        _mm512_xor_si512(_mm512_srli_epi64::<61>(hi), _mm512_srli_epi64::<60>(hi)),
    );
    let fold = |v| {
        _mm512_xor_si512(
            v,
            _mm512_xor_si512(
                _mm512_slli_epi64::<1>(v),
                _mm512_xor_si512(_mm512_slli_epi64::<3>(v), _mm512_slli_epi64::<4>(v)),
            ),
        )
    };
    _mm512_xor_si512(lo, _mm512_xor_si512(fold(hi), fold(overflow)))
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn reduce_cl(product: __m512i) -> __m512i {
    let polynomial = _mm512_set1_epi64(0x1b);
    let fold = _mm512_clmulepi64_epi128::<0x01>(product, polynomial);
    let overflow = _mm512_clmulepi64_epi128::<0x01>(fold, polynomial);
    _mm512_xor_si512(product, _mm512_xor_si512(fold, overflow))
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn multiply<const CL: bool>(a: __m512i, b: __m512i) -> __m512i {
    let (even, odd) = raw(a, b);
    if CL {
        _mm512_unpacklo_epi64(reduce_cl(even), reduce_cl(odd))
    } else {
        reduce_shift(
            _mm512_unpacklo_epi64(even, odd),
            _mm512_unpackhi_epi64(even, odd),
        )
    }
}

#[cfg(test)]
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn dot(a: &[u64], b: &[u64]) -> u64 {
    let mut even = _mm512_setzero_si512();
    let mut odd = even;
    for (a, b) in a.chunks(8).zip(b.chunks(8)) {
        let (low, high) = raw(load(a), load(b));
        even = _mm512_xor_si512(even, low);
        odd = _mm512_xor_si512(odd, high);
    }
    // XOR is carryless: one final scalar reduction suffices for every lane.
    let lo = horizontal_xor(_mm512_unpacklo_epi64(even, odd));
    let hi = horizontal_xor(_mm512_unpackhi_epi64(even, odd));
    <ScalarArithmetic as Arithmetic<crate::field::Gf64>>::reduce(RawProduct { lo, hi })
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64) {
    scale_kernel::<false>(dst, src, scale);
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn scale_kernel<const CL: bool>(dst: &mut [u64], src: &[u64], scale: u64) {
    if scale == 0 {
        return;
    }
    if scale == 1 {
        return xor_assign(dst, src);
    }
    let scale = _mm512_set1_epi64(i64::from_ne_bytes(scale.to_ne_bytes()));
    for (dst, src) in dst.chunks_mut(8).zip(src.chunks(8)) {
        store(
            dst,
            _mm512_xor_si512(load(dst), multiply::<CL>(load(src), scale)),
        );
    }
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "square_slice contract is exercised by the forced kernel corpus"
    )
)]
fn square_slice(dst: &mut [u64], src: &[u64]) {
    square_kernel::<false>(dst, src);
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
#[cfg_attr(
    not(test),
    allow(
        dead_code,
        reason = "square_slice contract is exercised by the forced kernel corpus"
    )
)]
fn square_kernel<const CL: bool>(dst: &mut [u64], src: &[u64]) {
    for (dst, src) in dst.chunks_mut(8).zip(src.chunks(8)) {
        let value = load(src);
        store(dst, multiply::<CL>(value, value));
    }
}

#[target_feature(enable = "avx512f")]
fn xor_assign(dst: &mut [u64], src: &[u64]) {
    for (dst, src) in dst.chunks_mut(8).zip(src.chunks(8)) {
        store(dst, _mm512_xor_si512(load(dst), load(src)));
    }
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn horner_many(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
    horner_kernel::<true>(coefficients, points, out);
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn horner_kernel<const CL: bool>(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
    let Some((&leading, rest)) = coefficients.split_last() else {
        out.fill(0);
        return;
    };
    for (points, out) in points.chunks(8).zip(out.chunks_mut(8)) {
        let points = load(points);
        let mut value = _mm512_set1_epi64(i64::from_ne_bytes(leading.to_ne_bytes()));
        for &coefficient in rest.iter().rev() {
            value = _mm512_xor_si512(
                multiply::<CL>(value, points),
                _mm512_set1_epi64(i64::from_ne_bytes(coefficient.to_ne_bytes())),
            );
        }
        store(out, value);
    }
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn insert(odd: &mut [u64], ids: &[u64]) {
    if odd.is_empty() || ids.is_empty() {
        return;
    }
    if ids.len() == 1 {
        match odd.len() {
            18 => return insert_18(odd, ids[0]),
            32 => return insert_32(odd, ids[0]),
            72 => return insert_single::<72>(odd, ids[0]),
            89 => return insert_single::<89>(odd, ids[0]),
            _ => {}
        }
    }
    // Sparse rows leave most lanes of the dependent tile unused. Reuse the
    // short single-ID power schedules before switching to parallel ID lanes.
    if ids.len() <= 4 {
        match odd.len() {
            18 | 72 | 89 => return insert_sparse(odd, ids),
            _ => {}
        }
    }
    for ids in ids.chunks(32) {
        match ids.len() {
            0 => {}
            1..=8 => insert_tile::<1, true>(odd, ids),
            9..=16 => insert_tile::<2, true>(odd, ids),
            _ => insert_tile::<4, false>(odd, ids),
        }
    }
}

// Re-enter single dispatch so the kernels keep one call site and their original
// inlining. Keep the sparse loop's register saves off the single-ID entry path.
#[inline(never)]
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn insert_sparse(odd: &mut [u64], ids: &[u64]) {
    for &id in ids {
        insert(odd, &[id]);
    }
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn insert_tile<const W: usize, const CL: bool>(odd: &mut [u64], ids: &[u64]) {
    let mut powers = [_mm512_setzero_si512(); W];
    let mut steps = powers;
    for ((power, step), ids) in powers.iter_mut().zip(&mut steps).zip(ids.chunks(8)) {
        *power = load(ids);
        *step = multiply::<CL>(*power, *power);
    }
    odd[0] ^= horizontal_xor(
        powers
            .iter()
            .copied()
            .fold(_mm512_setzero_si512(), |sum, p| _mm512_xor_si512(sum, p)),
    );
    for syndrome in &mut odd[1..] {
        let mut sum = _mm512_setzero_si512();
        for (power, &step) in powers.iter_mut().zip(&steps) {
            *power = multiply::<CL>(*power, step);
            sum = _mm512_xor_si512(sum, *power);
        }
        *syndrome ^= horizontal_xor(sum);
    }
}

#[cfg(test)]
pub(super) fn test_frobenius(word: u64, power: usize) -> u64 {
    let lane = power - 1;
    let mut result = 0;
    for (chunk, entries) in INSERT_BASES.six.iter().enumerate() {
        result ^= entries[((word >> (6 * chunk)) & 63) as usize][lane];
    }
    result
        ^ INSERT_BASES.five[0][((word >> 54) & 31) as usize][lane]
        ^ INSERT_BASES.five[1][(word >> 59) as usize][lane]
}

// Each lookup supplies all seven Frobenius powers of x. Nine six-bit chunks
// and two five-bit chunks cover the full ID with 640 cache-line entries (40 KiB).
// Alignment keeps an entry in one cache line; it imposes no alignment on sketches.
#[repr(C, align(64))]
struct InsertionBases {
    six: [[[u64; 8]; 64]; 9],
    five: [[[u64; 8]; 32]; 2],
}

#[expect(
    clippy::large_stack_arrays,
    reason = "evaluated only by the static initializer"
)]
const fn insertion_bases() -> InsertionBases {
    let mut maps = InsertionBases {
        six: [[[0; 8]; 64]; 9],
        five: [[[0; 8]; 32]; 2],
    };
    let mut bit = 0;
    while bit < 64 {
        let mut column = 1_u64 << bit;
        let mut power = 0;
        while power < 7 {
            column = map_square(column);
            let (chunk, shift, count) = if bit < 54 {
                (bit / 6, bit % 6, 64)
            } else {
                ((bit - 54) / 5, (bit - 54) % 5, 32)
            };
            let mut value = 1;
            while value < count {
                if value & (1 << shift) != 0 {
                    if bit < 54 {
                        maps.six[chunk][value][power] ^= column;
                    } else {
                        maps.five[chunk][value][power] ^= column;
                    }
                }
                value += 1;
            }
            power += 1;
        }
        bit += 1;
    }
    maps
}
static INSERT_BASES: InsertionBases = insertion_bases();

#[target_feature(enable = "avx512f")]
fn single_bases(id: u64) -> __m512i {
    let v0 = load(&INSERT_BASES.six[0][(id & 63) as usize]);
    let v1 = load(&INSERT_BASES.six[1][((id >> 6) & 63) as usize]);
    let v2 = load(&INSERT_BASES.six[2][((id >> 12) & 63) as usize]);
    let v3 = load(&INSERT_BASES.six[3][((id >> 18) & 63) as usize]);
    let v4 = load(&INSERT_BASES.six[4][((id >> 24) & 63) as usize]);
    let v5 = load(&INSERT_BASES.six[5][((id >> 30) & 63) as usize]);
    let v6 = load(&INSERT_BASES.six[6][((id >> 36) & 63) as usize]);
    let v7 = load(&INSERT_BASES.six[7][((id >> 42) & 63) as usize]);
    let v8 = load(&INSERT_BASES.six[8][((id >> 48) & 63) as usize]);
    let v9 = load(&INSERT_BASES.five[0][((id >> 54) & 31) as usize]);
    let v10 = load(&INSERT_BASES.five[1][(id >> 59) as usize]);
    let a = _mm512_xor_si512(v0, _mm512_xor_si512(v1, v2));
    let b = _mm512_xor_si512(v3, _mm512_xor_si512(v4, v5));
    let c = _mm512_xor_si512(v6, _mm512_xor_si512(v7, v8));
    let d = _mm512_xor_si512(v9, v10);
    _mm512_xor_si512(_mm512_xor_si512(a, b), _mm512_xor_si512(c, d))
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn insert_18(odd: &mut [u64], id: u64) {
    let (low, high, tail) = powers_18(id);
    let (low_words, rest) = odd[..18].split_at_mut(8);
    let (high_words, tail_words) = rest.split_at_mut(8);
    store(low_words, _mm512_xor_si512(load(low_words), low));
    store(high_words, _mm512_xor_si512(load(high_words), high));
    store(tail_words, _mm512_xor_si512(load(tail_words), tail));
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn encode_18(odd: &mut [u64], ids: &[u64]) {
    let (mut low, mut high, mut tail) = powers_18(ids[0]);
    if ids.len() == 2 {
        let (other_low, other_high, other_tail) = powers_18(ids[1]);
        low = _mm512_xor_si512(low, other_low);
        high = _mm512_xor_si512(high, other_high);
        tail = _mm512_xor_si512(tail, other_tail);
    }
    let (low_words, rest) = odd[..18].split_at_mut(8);
    let (high_words, tail_words) = rest.split_at_mut(8);
    store(low_words, low);
    store(high_words, high);
    store(tail_words, tail);
}

#[inline]
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn powers_18(id: u64) -> (__m512i, __m512i, __m512i) {
    let x = _mm512_set1_epi64(i64::from_ne_bytes(id.to_ne_bytes()));
    let base = single_bases(id);
    // The spare first-level lane computes x^24 = x^8 * x^16,
    // avoiding a separate Frobenius lookup on the cube.
    // First: x^3,x^5,x^9,x^17,x^33. Second: x^7,x^11,x^13,x^19,x^21,x^25,x^35.
    let first = multiply::<true>(
        _mm512_mask_mov_epi64(
            x,
            0x20,
            _mm512_permutexvar_epi64(_mm512_set_epi64(2, 2, 2, 2, 2, 2, 2, 2), base),
        ),
        _mm512_mask_mov_epi64(
            base,
            0x20,
            _mm512_permutexvar_epi64(_mm512_set_epi64(3, 3, 3, 3, 3, 3, 3, 3), base),
        ),
    );
    let second = multiply::<true>(
        _mm512_permutexvar_epi64(_mm512_set_epi64(5, 0, 2, 1, 0, 1, 0, 0), first),
        _mm512_permutexvar_epi64(_mm512_set_epi64(5, 4, 3, 3, 3, 2, 2, 1), base),
    );
    let right = _mm512_permutexvar_epi64(_mm512_set_epi64(5, 5, 5, 0, 3, 3, 3, 2), base);
    let right = _mm512_mask_mov_epi64(
        right,
        0x10,
        _mm512_permutexvar_epi64(_mm512_set_epi64(5, 5, 5, 5, 5, 5, 5, 5), first),
    );
    // Third: x^15,x^23,x^27,x^29,x^31. Keep products in registers until the row update.
    let third = multiply::<true>(
        _mm512_permutexvar_epi64(_mm512_set_epi64(7, 7, 7, 0, 2, 1, 0, 0), second),
        right,
    );
    let low = _mm512_permutex2var_epi64(first, _mm512_set_epi64(0, 10, 9, 2, 8, 1, 0, 0), second);
    let low = _mm512_permutex2var_epi64(low, _mm512_set_epi64(8, 6, 5, 4, 3, 2, 1, 0), third);
    let low = _mm512_mask_mov_epi64(low, 1, x);
    let high =
        _mm512_permutex2var_epi64(first, _mm512_set_epi64(0, 0, 0, 13, 0, 12, 11, 3), second);
    let high = _mm512_permutex2var_epi64(high, _mm512_set_epi64(12, 11, 10, 4, 9, 2, 1, 0), third);
    let tail = _mm512_permutex2var_epi64(first, _mm512_set_epi64(0, 0, 0, 0, 0, 0, 14, 4), second);
    (low, high, tail)
}

// Three multiplication levels, with spare lanes carrying even powers needed
// by later levels. Five vector multiplies replace the six of block doubling;
// the exponent layouts below make each literal permutation auditable.
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn insert_32(odd: &mut [u64], id: u64) {
    let odd = &mut odd[..32];
    let base = single_bases(id);
    let x = _mm512_set1_epi64(i64::from_ne_bytes(id.to_ne_bytes()));
    // first: x^3,x^5,x^9,x^17,x^33,x^12,x^24,x^48.
    let first = multiply::<true>(
        _mm512_permutex2var_epi64(x, _mm512_set_epi64(11, 10, 9, 0, 0, 0, 0, 0), base),
        _mm512_permutexvar_epi64(_mm512_set_epi64(4, 3, 2, 4, 3, 2, 1, 0), base),
    );
    // second_low: x^7,x^11,x^13,x^19,x^21,x^25,x^35,x^37.
    let second_low = multiply::<true>(
        _mm512_permutexvar_epi64(_mm512_set_epi64(1, 0, 2, 1, 0, 1, 0, 0), first),
        _mm512_permutexvar_epi64(_mm512_set_epi64(4, 4, 3, 3, 3, 2, 2, 1), base),
    );
    // second_high: x^41,x^49,x^15,x^27,x^29,x^51,x^40,x^56.
    let second_high = multiply::<true>(
        _mm512_permutex2var_epi64(first, _mm512_set_epi64(6, 10, 0, 1, 0, 0, 3, 2), base),
        _mm512_permutex2var_epi64(base, _mm512_set_epi64(4, 4, 15, 14, 14, 13, 4, 4), first),
    );
    // third_low: x^23,x^31,x^39,x^43,x^45,x^47,x^53,x^55.
    let third_low = multiply::<true>(
        _mm512_permutex2var_epi64(second_low, _mm512_set_epi64(0, 9, 0, 9, 8, 0, 0, 0), first),
        _mm512_mask_mov_epi64(
            _mm512_permutex2var_epi64(base, _mm512_set_epi64(15, 15, 0, 0, 0, 4, 14, 3), first),
            56,
            _mm512_permutexvar_epi64(_mm512_set_epi64(0, 0, 6, 6, 6, 0, 0, 0), second_high),
        ),
    );
    // third_high: x^57,x^59,x^61,x^63 (remaining lanes unused).
    let third_high = multiply::<true>(
        _mm512_permutex2var_epi64(first, _mm512_set_epi64(0, 0, 0, 0, 8, 1, 0, 2), second_low),
        _mm512_permutex2var_epi64(
            first,
            _mm512_set_epi64(0, 0, 0, 0, 15, 15, 15, 7),
            second_high,
        ),
    );
    let value = _mm512_mask_mov_epi64(
        _mm512_mask_mov_epi64(
            _mm512_permutex2var_epi64(x, _mm512_set_epi64(0, 0, 0, 10, 0, 9, 8, 0), first),
            104,
            _mm512_permutexvar_epi64(_mm512_set_epi64(0, 2, 1, 0, 0, 0, 0, 0), second_low),
        ),
        128,
        _mm512_permutexvar_epi64(_mm512_set_epi64(2, 0, 0, 0, 0, 0, 0, 0), second_high),
    );
    let dst = &mut odd[0..8];
    store(dst, _mm512_xor_si512(load(dst), value));
    let value = _mm512_mask_mov_epi64(
        _mm512_mask_mov_epi64(
            _mm512_permutex2var_epi64(
                first,
                _mm512_set_epi64(0, 0, 0, 13, 0, 12, 11, 3),
                second_low,
            ),
            136,
            _mm512_permutexvar_epi64(_mm512_set_epi64(1, 0, 0, 0, 0, 0, 0, 0), third_low),
        ),
        96,
        _mm512_permutexvar_epi64(_mm512_set_epi64(0, 4, 3, 0, 0, 0, 0, 0), second_high),
    );
    let dst = &mut odd[8..16];
    store(dst, _mm512_xor_si512(load(dst), value));
    let value = _mm512_mask_mov_epi64(
        _mm512_mask_mov_epi64(
            _mm512_permutex2var_epi64(
                first,
                _mm512_set_epi64(0, 0, 0, 0, 0, 15, 14, 4),
                second_low,
            ),
            232,
            _mm512_permutexvar_epi64(_mm512_set_epi64(5, 4, 3, 0, 2, 0, 0, 0), third_low),
        ),
        16,
        _mm512_permutexvar_epi64(_mm512_set_epi64(0, 0, 0, 0, 0, 0, 0, 0), second_high),
    );
    let dst = &mut odd[16..24];
    store(dst, _mm512_xor_si512(load(dst), value));
    let value = _mm512_mask_mov_epi64(
        _mm512_permutex2var_epi64(
            second_high,
            _mm512_set_epi64(0, 0, 0, 0, 15, 14, 5, 1),
            third_low,
        ),
        240,
        _mm512_permutexvar_epi64(_mm512_set_epi64(3, 2, 1, 0, 0, 0, 0, 0), third_high),
    );
    let dst = &mut odd[24..32];
    store(dst, _mm512_xor_si512(load(dst), value));
}

// Start with x,x^3,...,x^15. Multiplication by x^16 doubles this to
// sixteen odd powers; x^32, x^64 and x^128 repeat the same operation on
// independent register blocks. Unlike a runtime schedule, every bound and
// broadcast below is constant for both supported capacities.
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn insert_single<const C: usize>(odd: &mut [u64], id: u64) {
    let odd = &mut odd[..C];
    let base = single_bases(id);
    let x = _mm512_set1_epi64(i64::from_ne_bytes(id.to_ne_bytes()));
    let b = multiply::<true>(x, broadcast::<0>(base));
    let a = _mm512_unpacklo_epi64(x, b);
    let b = multiply::<true>(a, broadcast::<1>(base));
    let a = _mm512_permutex2var_epi64(a, _mm512_set_epi64(9, 8, 1, 0, 9, 8, 1, 0), b);
    let b = multiply::<true>(a, broadcast::<2>(base));
    let v0 = _mm512_permutex2var_epi64(a, _mm512_set_epi64(11, 10, 9, 8, 3, 2, 1, 0), b);
    update_single_block(odd, 0, v0);
    let v1 = multiply::<true>(v0, broadcast::<3>(base));
    update_single_block(odd, 8, v1);
    let v2 = multiply::<true>(v0, broadcast::<4>(base));
    update_single_block(odd, 16, v2);
    let v3 = multiply::<true>(v1, broadcast::<4>(base));
    update_single_block(odd, 24, v3);
    if C > 32 {
        let step = broadcast::<5>(base);
        let v4 = multiply::<true>(v0, step);
        let v5 = multiply::<true>(v1, step);
        let v6 = multiply::<true>(v2, step);
        let v7 = multiply::<true>(v3, step);
        update_single_block(odd, 32, v4);
        update_single_block(odd, 40, v5);
        update_single_block(odd, 48, v6);
        update_single_block(odd, 56, v7);
        let step = broadcast::<6>(base);
        update_single_block(odd, 64, multiply::<true>(v0, step));
        if C > 72 {
            update_single_block(odd, 72, multiply::<true>(v1, step));
            update_single_block(odd, 80, multiply::<true>(v2, step));
            update_single_block(odd, 88, multiply::<true>(v3, step));
        }
    }
}

#[target_feature(enable = "avx512f")]
fn broadcast<const LANE: i64>(value: __m512i) -> __m512i {
    _mm512_permutexvar_epi64(_mm512_set1_epi64(LANE), value)
}

#[target_feature(enable = "avx512f")]
fn update_single_block(odd: &mut [u64], offset: usize, value: __m512i) {
    let end = (offset + 8).min(odd.len());
    let dst = &mut odd[offset..end];
    store(dst, _mm512_xor_si512(load(dst), value));
}

#[cfg(test)]
pub(super) fn test_products(a: &[u64; 8], b: &[u64; 8]) -> ([u64; 8], [u64; 8]) {
    assert!(available());
    // SAFETY: this test interface enforces the hardware/OS gate itself.
    unsafe { product_words(a, b) }
}

#[cfg(test)]
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn product_words(a: &[u64; 8], b: &[u64; 8]) -> ([u64; 8], [u64; 8]) {
    let (even, odd) = raw(load(a), load(b));
    let (mut lo, mut hi) = ([0; 8], [0; 8]);
    store(&mut lo, _mm512_unpacklo_epi64(even, odd));
    store(&mut hi, _mm512_unpackhi_epi64(even, odd));
    (lo, hi)
}

#[cfg(test)]
pub(super) fn test_reductions(lo: &[u64; 8], hi: &[u64; 8]) -> ([u64; 8], [u64; 8]) {
    assert!(available());
    // SAFETY: this test interface enforces the hardware/OS gate itself.
    unsafe { reduction_words(lo, hi) }
}

#[cfg(test)]
#[target_feature(enable = "avx512f,vpclmulqdq")]
fn reduction_words(lo: &[u64; 8], hi: &[u64; 8]) -> ([u64; 8], [u64; 8]) {
    let (lo, hi) = (load(lo), load(hi));
    let even = _mm512_unpacklo_epi64(lo, hi);
    let odd = _mm512_unpackhi_epi64(lo, hi);
    let (mut shift, mut cl) = ([0; 8], [0; 8]);
    store(&mut shift, reduce_shift(lo, hi));
    store(
        &mut cl,
        _mm512_unpacklo_epi64(reduce_cl(even), reduce_cl(odd)),
    );
    (shift, cl)
}

#[target_feature(enable = "avx512f")]
fn difference(dst: &mut [u64], local: &[u64], remote: &[u8]) -> bool {
    let mut any = _mm512_setzero_si512();
    for offset in (0..dst.len()).step_by(8) {
        let n = (dst.len() - offset).min(8);
        // SAFETY: offset..offset+n is in each slice; remote has eight bytes per
        // word. Masked unaligned loads admit every byte alignment and short tail.
        let delta = unsafe {
            _mm512_xor_si512(
                load(&local[offset..offset + n]),
                _mm512_maskz_loadu_epi64(mask(n), remote.as_ptr().add(8 * offset).cast()),
            )
        };
        store(&mut dst[offset..offset + n], delta);
        any = _mm512_or_si512(any, delta);
    }
    _mm512_test_epi64_mask(any, any) != 0
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn multiply_linear(coefficients: &mut [u64], root: u64) {
    let root = _mm512_set1_epi64(i64::from_ne_bytes(root.to_ne_bytes()));
    let mut end = coefficients.len();
    while end > 1 {
        let start = end.saturating_sub(8).max(1);
        // Descending blocks preserve every source coefficient until it is read.
        let value = _mm512_xor_si512(
            load(&coefficients[start..end]),
            multiply::<true>(load(&coefficients[start - 1..end - 1]), root),
        );
        store(&mut coefficients[start..end], value);
        end = start;
    }
}

#[target_feature(enable = "avx512f,vpclmulqdq")]
fn odd_recurrence_matches(odd: &[u64], squared_locator: &[u64]) -> bool {
    let degree = squared_locator.len() - 1;
    for index in (degree..odd.len()).step_by(8) {
        let len = (odd.len() - index).min(8);
        let mut even = _mm512_setzero_si512();
        let mut high = even;
        for lag in 1..=degree {
            let (low, upper) = raw(
                load(&odd[index - lag..index - lag + len]),
                _mm512_set1_epi64(i64::from_ne_bytes(squared_locator[lag].to_ne_bytes())),
            );
            even = _mm512_xor_si512(even, low);
            high = _mm512_xor_si512(high, upper);
        }
        let expected = _mm512_unpacklo_epi64(reduce_cl(even), reduce_cl(high));
        let mismatch = _mm512_xor_si512(expected, load(&odd[index..index + len]));
        if _mm512_test_epi64_mask(mismatch, _mm512_set1_epi64(-1)) & mask(len) != 0 {
            return false;
        }
    }
    true
}
