#![forbid(unsafe_code)]

use crate::{
    backend::{
        contract::{Arithmetic, BulkKernels},
        detect::resolve,
        portable::Portable,
    },
    field::{
        BinaryField, Gf64, reference,
        tiny::{Gf4, Gf16, Gf256, Gf65536},
    },
    types::{BackendError, BackendId, BackendRequest, RawProduct},
};

macro_rules! all_fields {
    ($check:ident) => {
        $check::<Gf64>();
        $check::<Gf4>();
        $check::<Gf16>();
        $check::<Gf256>();
        $check::<Gf65536>();
    };
}

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut word = *state;
    word = (word ^ (word >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    word = (word ^ (word >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    word ^ (word >> 31)
}

fn words<F: BinaryField>(len: usize, mut seed: u64) -> Vec<u64> {
    (0..len)
        .map(|_| (next(&mut seed) & F::MASK).max(1))
        .collect()
}

fn reference_frobenius<F: BinaryField>(mut value: u64, power: u32) -> u64 {
    for _ in 0..power {
        value = reference::mul::<F>(value, value);
    }
    value
}

fn reference_trace<F: BinaryField>(value: u64) -> u8 {
    let mut sum = 0;
    let mut conjugate = value;
    for _ in 0..F::BITS {
        sum ^= conjugate;
        conjugate = reference::mul::<F>(conjugate, conjugate);
    }
    u8::try_from(sum).expect("reference trace is a bit")
}

fn reference_inverse<F: BinaryField>(value: u64) -> Option<u64> {
    if value == 0 {
        return None;
    }
    let mut remainders = [
        u128::from(value),
        (1_u128 << F::BITS) | u128::from(F::MODULUS_LOW),
    ];
    let mut coefficients = [1_u128, 0];
    while remainders[0] != 1 {
        assert_ne!(remainders[0], 0, "irreducible modulus bits={}", F::BITS);
        if remainders[0].leading_zeros() > remainders[1].leading_zeros() {
            remainders.swap(0, 1);
            coefficients.swap(0, 1);
        }
        let shift = remainders[1].leading_zeros() - remainders[0].leading_zeros();
        remainders[0] ^= remainders[1] << shift;
        coefficients[0] ^= coefficients[1] << shift;
    }
    Some(reference::reduce::<F>(RawProduct {
        lo: u64::try_from(coefficients[0] & u128::from(u64::MAX)).unwrap(),
        hi: u64::try_from(coefficients[0] >> 64).unwrap(),
    }))
}

fn check_arithmetic<F: BinaryField>() {
    let mut values = vec![0, 1, F::MASK, F::MASK >> 1, 0xaaaa_aaaa_aaaa_aaaa & F::MASK];
    values.extend((0..F::BITS).map(|bit| 1 << bit));
    values.extend(0..=F::MASK.min(255));
    values.extend(words::<F>(256, 0x534b_4e43_4c32_0001));
    for &a in &values {
        assert_eq!(
            <Portable as Arithmetic<F>>::square(a),
            reference::mul::<F>(a, a),
            "square bits={} a={a:#x}",
            F::BITS
        );
        assert_eq!(
            <Portable as Arithmetic<F>>::inverse(a),
            reference_inverse::<F>(a),
            "inverse bits={} a={a:#x}",
            F::BITS
        );
        let trace = reference_trace::<F>(a);
        assert_eq!(
            <Portable as Arithmetic<F>>::trace(a),
            trace,
            "trace bits={} a={a:#x}",
            F::BITS
        );
        match <Portable as Arithmetic<F>>::solve_quadratic(a) {
            Some(root) => {
                assert_eq!(trace, 0, "quadratic accepted bits={} a={a:#x}", F::BITS);
                assert_eq!(
                    root & 1,
                    0,
                    "quadratic convention bits={} a={a:#x}",
                    F::BITS
                );
                assert_eq!(
                    reference::mul::<F>(root, root) ^ root,
                    a,
                    "quadratic solution bits={} a={a:#x} root={root:#x}",
                    F::BITS
                );
            }
            None => assert_eq!(trace, 1, "quadratic rejected bits={} a={a:#x}", F::BITS),
        }
        for power in [0, 1, F::BITS - 1, F::BITS, F::BITS + 1, u32::MAX] {
            assert_eq!(
                <Portable as Arithmetic<F>>::frobenius(a, power),
                reference_frobenius::<F>(a, power % F::BITS),
                "frobenius bits={} a={a:#x} power={power}",
                F::BITS
            );
        }
        for &b in &values[..5] {
            assert_eq!(
                <Portable as Arithmetic<F>>::raw_mul(a, b),
                reference::raw_mul::<F>(a, b),
                "raw_mul bits={} a={a:#x} b={b:#x}",
                F::BITS
            );
            assert_eq!(
                <Portable as Arithmetic<F>>::mul(a, b),
                reference::mul::<F>(a, b),
                "mul bits={} a={a:#x} b={b:#x}",
                F::BITS
            );
        }
    }
    let mut state = 0x534b_4e43_4c32_0002;
    for bit in 0..384 {
        let product = if bit < 128 {
            RawProduct {
                lo: if bit < 64 { 1 << bit } else { 0 },
                hi: if bit >= 64 { 1 << (bit - 64) } else { 0 },
            }
        } else {
            RawProduct {
                lo: next(&mut state),
                hi: next(&mut state),
            }
        };
        assert_eq!(
            <Portable as Arithmetic<F>>::reduce(product),
            reference::reduce::<F>(product),
            "reduce bits={} product={product:?}",
            F::BITS
        );
    }
}

#[test]
fn arithmetic_matches_oracles() {
    all_fields!(check_arithmetic);
}

fn reference_dot<F: BinaryField>(a: &[u64], b: &[u64]) -> u64 {
    a.iter()
        .zip(b)
        .fold(0, |sum, (&a, &b)| sum ^ reference::mul::<F>(a, b))
}

fn check_dot<F: BinaryField>() {
    for len in (0..=17).chain([31, 32, 33, 63, 64, 65, 127, 128, 129, 1024]) {
        let mut left = words::<F>(len + 16, 11);
        left[8] = 0;
        let right = words::<F>(len + 16, 29);
        for a in 0..=8 {
            for b in 0..=8 {
                assert_eq!(
                    <Portable as Arithmetic<F>>::dot(&left[a..a + len], &right[b..b + len]),
                    reference_dot::<F>(&left[a..a + len], &right[b..b + len]),
                    "dot bits={} len={len} offsets={a},{b}",
                    F::BITS
                );
            }
        }
    }
}

#[test]
fn dot_tails_and_offsets() {
    all_fields!(check_dot);
}

fn check_slices<F: BinaryField>(operation: &str) {
    for len in 0..=17 {
        let mut src = words::<F>(len + 16, 41);
        src[8] = 0;
        for source in 0..=8 {
            for target in 0..=8 {
                for scale in [0, 1, F::MASK] {
                    let mut actual = words::<F>(len + 16, 59);
                    let mut expected = actual.clone();
                    for i in 0..len {
                        let value = src[source + i];
                        match operation {
                            "scale_xor" => {
                                expected[target + i] ^= reference::mul::<F>(value, scale);
                            }
                            "square_slice" => {
                                expected[target + i] = reference::mul::<F>(value, value);
                            }
                            "xor_assign" => expected[target + i] ^= value,
                            _ => unreachable!(),
                        }
                    }
                    let dst = &mut actual[target..target + len];
                    let src = &src[source..source + len];
                    match operation {
                        "scale_xor" => <Portable as Arithmetic<F>>::scale_xor(dst, src, scale),
                        "square_slice" => <Portable as Arithmetic<F>>::square_slice(dst, src),
                        "xor_assign" => <Portable as BulkKernels<F>>::xor_assign(dst, src),
                        _ => unreachable!(),
                    }
                    assert_eq!(
                        actual,
                        expected,
                        "{operation} bits={} len={len} offsets={source},{target} scale={scale:#x}",
                        F::BITS
                    );
                }
            }
        }
    }
}

#[test]
fn scale_xor_tails_and_offsets() {
    check_slices::<Gf64>("scale_xor");
    check_slices::<Gf4>("scale_xor");
    check_slices::<Gf16>("scale_xor");
    check_slices::<Gf256>("scale_xor");
    check_slices::<Gf65536>("scale_xor");
}

#[test]
fn square_slice_tails_and_offsets() {
    check_slices::<Gf64>("square_slice");
    check_slices::<Gf4>("square_slice");
    check_slices::<Gf16>("square_slice");
    check_slices::<Gf256>("square_slice");
    check_slices::<Gf65536>("square_slice");
}

#[test]
fn xor_assign_tails_and_offsets() {
    check_slices::<Gf64>("xor_assign");
    check_slices::<Gf4>("xor_assign");
    check_slices::<Gf16>("xor_assign");
    check_slices::<Gf256>("xor_assign");
    check_slices::<Gf65536>("xor_assign");
}

fn reference_eval<F: BinaryField>(coefficients: &[u64], point: u64) -> u64 {
    let mut result = 0;
    let mut power = 1;
    for &coefficient in coefficients {
        result ^= reference::mul::<F>(coefficient, power);
        power = reference::mul::<F>(power, point);
    }
    result
}

fn check_horner<F: BinaryField>() {
    for coefficient_len in 0..=17 {
        let mut coefficients = words::<F>(coefficient_len + 16, 61);
        coefficients[8] = 0;
        for len in 0..=17 {
            for offset in 0..=8 {
                let target = 8 - offset;
                let coefficients = &coefficients[offset..offset + coefficient_len];
                let mut points = words::<F>(len + 16, 71);
                points[offset] = 0;
                let mut actual = words::<F>(len + 16, 83);
                let mut expected = actual.clone();
                for i in 0..len {
                    expected[target + i] = reference_eval::<F>(coefficients, points[offset + i]);
                }
                <Portable as BulkKernels<F>>::horner_many(
                    coefficients,
                    &points[offset..offset + len],
                    &mut actual[target..target + len],
                );
                assert_eq!(
                    actual,
                    expected,
                    "horner bits={} coefficients={coefficient_len} len={len} \
                     offsets={offset},{target}",
                    F::BITS
                );
            }
        }
    }
}

#[test]
fn horner_tails_and_offsets() {
    all_fields!(check_horner);
}

fn reference_insert<F: BinaryField>(odd: &mut [u64], ids: &[u64]) {
    for (index, syndrome) in odd.iter_mut().enumerate() {
        for &id in ids {
            let mut power = 1;
            let mut base = id;
            let mut exponent = 2 * index + 1;
            while exponent != 0 {
                if exponent & 1 != 0 {
                    power = reference::mul::<F>(power, base);
                }
                base = reference::mul::<F>(base, base);
                exponent >>= 1;
            }
            *syndrome ^= power;
        }
    }
}

fn check_insert<F: BinaryField>() {
    for capacity in (0..=18).chain([72, 89]) {
        for count in 0..=17 {
            for offset in 0..=8 {
                let target = 8 - offset;
                let ids = words::<F>(count + 16, 97);
                let ids = &ids[offset..offset + count];
                let initial = words::<F>(capacity + 16, 101);
                let mut actual = initial.clone();
                let mut expected = initial.clone();
                reference_insert::<F>(&mut expected[target..target + capacity], ids);
                <Portable as BulkKernels<F>>::insert_nonzero(
                    &mut actual[target..target + capacity],
                    ids,
                );
                assert_eq!(
                    actual,
                    expected,
                    "insert bits={} c={capacity} ids={count} offsets={offset},{target}",
                    F::BITS
                );
                let mut singles = initial.clone();
                for id in ids {
                    <Portable as BulkKernels<F>>::insert_nonzero(
                        &mut singles[target..target + capacity],
                        &[*id],
                    );
                }
                assert_eq!(
                    singles,
                    expected,
                    "arrival chunks bits={} c={capacity} ids={ids:?}",
                    F::BITS
                );
                let mut reversed = initial.clone();
                let reverse: Vec<_> = ids.iter().rev().copied().collect();
                <Portable as BulkKernels<F>>::insert_nonzero(
                    &mut reversed[target..target + capacity],
                    &reverse,
                );
                assert_eq!(
                    reversed,
                    expected,
                    "permutation bits={} c={capacity} ids={ids:?}",
                    F::BITS
                );
                <Portable as BulkKernels<F>>::insert_nonzero(
                    &mut actual[target..target + capacity],
                    ids,
                );
                assert_eq!(
                    actual,
                    initial,
                    "parity bits={} c={capacity} ids={ids:?}",
                    F::BITS
                );
                if count == 1 {
                    <Portable as BulkKernels<F>>::insert_nonzero(
                        &mut actual[target..target + capacity],
                        &[ids[0], ids[0]],
                    );
                    assert_eq!(
                        actual,
                        initial,
                        "duplicate in one call bits={} c={capacity} id={:#x}",
                        F::BITS,
                        ids[0]
                    );
                }
            }
        }
    }
}

#[test]
fn insert_odd_powers_and_parity() {
    all_fields!(check_insert);
}

#[test]
fn dimensions_fail_before_writes() {
    for (short, long) in [(0, 1), (1, 2), (8, 9), (16, 17)] {
        for (dst_len, src_len) in [(short, long), (long, short)] {
            let src = words::<Gf64>(src_len, 103);
            for operation in ["scale_xor", "square_slice", "xor_assign", "horner_many"] {
                let mut dst = words::<Gf64>(dst_len, 107);
                let initial = dst.clone();
                let failure =
                    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| match operation {
                        "scale_xor" => <Portable as Arithmetic<Gf64>>::scale_xor(&mut dst, &src, 3),
                        "square_slice" => {
                            <Portable as Arithmetic<Gf64>>::square_slice(&mut dst, &src);
                        }
                        "xor_assign" => <Portable as BulkKernels<Gf64>>::xor_assign(&mut dst, &src),
                        "horner_many" => {
                            <Portable as BulkKernels<Gf64>>::horner_many(&[1, 2], &src, &mut dst);
                        }
                        _ => unreachable!(),
                    }));
                assert!(
                    failure.is_err(),
                    "{operation} accepted lengths {dst_len},{src_len}"
                );
                assert_eq!(dst, initial, "{operation} wrote before dimension check");
            }
            assert!(
                std::panic::catch_unwind(|| <Portable as Arithmetic<Gf64>>::dot(
                    &src,
                    &vec![1; dst_len]
                ))
                .is_err(),
                "dot accepted lengths {dst_len},{src_len}"
            );
        }
    }
}

#[test]
fn only_portable_is_available() {
    let _unavailable = crate::backend::detect::without_vector();
    assert_eq!(resolve(BackendRequest::Auto), Ok(BackendId::Portable));
    for id in [
        BackendId::Portable,
        BackendId::Pclmul,
        BackendId::Vpclmul256,
        BackendId::Vpclmul512,
    ] {
        let expected = if id == BackendId::Portable {
            Ok(id)
        } else {
            Err(BackendError(id))
        };
        assert_eq!(
            resolve(BackendRequest::Force(id)),
            expected,
            "forced backend {id:?}"
        );
    }
}
