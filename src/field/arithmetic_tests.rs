#![forbid(unsafe_code)]

use crate::{
    field::{
        BinaryField, Gf64, gf64, maps, reference,
        tiny::{Gf4, Gf16, Gf256, Gf65536},
    },
    types::RawProduct,
};

const SEED: u64 = 0x534b_4e43_4c31_0001;

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut word = *state;
    word = (word ^ (word >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    word = (word ^ (word >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    word ^ (word >> 31)
}

#[test]
fn gf64_products() {
    assert_eq!(
        gf64::frobenius::<Gf64>(1 << 63, 1),
        0xc000_0000_0000_005a,
        "Frobenius square"
    );
    // Z^63*Z = Z^64 = Z^4+Z^3+Z+1. Multiplying by Z once more gives 0x36.
    // Z^63*Z^63 = Z^126 = Z^66+Z^65+Z^63+Z^62 = 0xc000...005a,
    // because Z^66 -> 0x6c and Z^65 -> 0x36 (XOR, not integer addition).
    for (a, b, expected) in [
        (1_u64 << 63, 2, 0x1b),
        (1 << 63, 4, 0x36),
        (1 << 63, 1 << 63, 0xc000_0000_0000_005a),
        (0x1b, 0x1b, 0x145), // (Z^4+Z^3+Z+1)^2 = Z^8+Z^6+Z^2+1.
    ] {
        assert_eq!(gf64::mul::<Gf64>(a, b), expected, "GF64 hand vector");
        assert_eq!(reference::mul::<Gf64>(a, b), expected, "oracle hand vector");
    }
    for i in 0..64 {
        for j in 0..64 {
            check_product::<Gf64>(1 << i, 1 << j);
        }
    }
    let patterns = [
        0,
        1,
        u64::MAX,
        1 << 63,
        u64::MAX >> 1,
        0xaaaa_aaaa_aaaa_aaaa,
        0x5555_5555_5555_5555,
    ];
    for a in patterns {
        for b in patterns {
            check_product::<Gf64>(a, b);
        }
    }
    let mut state = SEED;
    for _ in 0..8192 {
        check_product::<Gf64>(next(&mut state), next(&mut state));
        let product = RawProduct {
            lo: next(&mut state),
            hi: next(&mut state),
        };
        assert_eq!(
            gf64::reduce::<Gf64>(product),
            reference::reduce::<Gf64>(product),
            "arbitrary raw reduction bits={} product={product:?}",
            Gf64::BITS
        );
    }
    for bit in 0..128 {
        let product = if bit < 64 {
            RawProduct {
                lo: 1 << bit,
                hi: 0,
            }
        } else {
            RawProduct {
                lo: 0,
                hi: 1 << (bit - 64),
            }
        };
        assert_eq!(
            gf64::reduce::<Gf64>(product),
            reference::reduce::<Gf64>(product),
            "raw basis reduction bit {bit}"
        );
    }
}

fn check_product<F: crate::field::BinaryField>(a: u64, b: u64) {
    assert_eq!(
        gf64::raw_mul::<F>(a, b),
        reference::raw_mul::<F>(a, b),
        "raw product a={a:#x} b={b:#x}"
    );
    assert_eq!(
        gf64::mul::<F>(a, b),
        reference::mul::<F>(a, b),
        "field product a={a:#x} b={b:#x}"
    );
    assert_eq!(
        gf64::square::<F>(a),
        reference::mul::<F>(a, a),
        "square a={a:#x}"
    );
}

#[expect(
    clippy::cast_possible_truncation,
    reason = "split an extended-Euclid polynomial into words"
)]
fn euclid_inverse<F: BinaryField>(a: u64) -> Option<u64> {
    if a == 0 {
        return None;
    }
    let (mut remainder, mut other_remainder) = (
        u128::from(a),
        (1_u128 << F::BITS) | u128::from(F::MODULUS_LOW),
    );
    let (mut coefficient, mut other_coefficient) = (1_u128, 0_u128);
    while remainder != 1 {
        assert_ne!(remainder, 0, "modulus must be irreducible");
        if remainder.leading_zeros() > other_remainder.leading_zeros() {
            std::mem::swap(&mut remainder, &mut other_remainder);
            std::mem::swap(&mut coefficient, &mut other_coefficient);
        }
        let shift = other_remainder.leading_zeros() - remainder.leading_zeros();
        remainder ^= other_remainder << shift;
        coefficient ^= other_coefficient << shift;
    }
    Some(reference::reduce::<F>(RawProduct {
        lo: coefficient as u64,
        hi: (coefficient >> 64) as u64,
    }))
}

#[test]
fn gf64_inverse() {
    assert_eq!(maps::inverse::<Gf64>(0), None, "zero has no inverse");
    for a in [1, 2, 0x1b, 1 << 63, u64::MAX] {
        check_inverse::<Gf64>(a);
    }
    let mut state = SEED;
    for _ in 0..4096 {
        check_inverse::<Gf64>(next(&mut state));
    }
}

fn check_inverse<F: BinaryField>(a: u64) {
    let actual = maps::inverse::<F>(a);
    assert_eq!(
        actual,
        euclid_inverse::<F>(a),
        "Itoh-Tsujii vs Euclid a={a:#x}"
    );
    if let Some(inverse) = actual {
        assert_eq!(gf64::mul::<F>(a, inverse), 1, "inverse identity a={a:#x}");
        assert_eq!(
            reference::mul::<F>(a, inverse),
            1,
            "oracle inverse identity a={a:#x}"
        );
    }
}

fn oracle_trace<F: BinaryField>(a: u64) -> u8 {
    let mut power = a;
    let mut sum = 0;
    for _ in 0..F::BITS {
        sum ^= power;
        power = reference::mul::<F>(power, power);
    }
    assert!(sum <= 1, "oracle trace is a bit");
    u8::try_from(sum).expect("trace is a bit")
}

fn check_unary<F: BinaryField>(a: u64) {
    assert_eq!(
        gf64::square::<F>(a),
        reference::mul::<F>(a, a),
        "unary square a={a:#x}"
    );
    check_inverse::<F>(a);
    let mut conjugate = a;
    for _ in 0..F::BITS {
        conjugate = gf64::square::<F>(conjugate);
    }
    assert_eq!(conjugate, a, "Frobenius periodicity a={a:#x}");
    for power in [0, 1, F::BITS, F::BITS + 1, u32::MAX] {
        let mut expected = a;
        for _ in 0..power % F::BITS {
            expected = reference::mul::<F>(expected, expected);
        }
        assert_eq!(
            gf64::frobenius::<F>(a, power),
            expected,
            "Frobenius power={power} a={a:#x}"
        );
    }
    let trace = maps::trace::<F>(a);
    assert_eq!(trace, oracle_trace::<F>(a), "absolute trace a={a:#x}");
    match maps::solve_quadratic::<F>(a) {
        Some(z) => {
            assert_eq!(trace, 0, "trace-one input accepted");
            assert_eq!(z & 1, 0, "quadratic free coordinate");
            assert_eq!(
                reference::mul::<F>(z, z) ^ z,
                a,
                "quadratic solution a={a:#x}"
            );
        }
        None => assert_eq!(trace, 1, "trace-zero input rejected a={a:#x}"),
    }
}

fn check_laws<F: BinaryField>(a: u64, b: u64, c: u64) {
    assert_eq!(
        gf64::mul::<F>(a, b),
        gf64::mul::<F>(b, a),
        "commutativity bits={} a={a:#x} b={b:#x} c={c:#x}",
        F::BITS
    );
    assert_eq!(
        gf64::mul::<F>(a, gf64::mul::<F>(b, c)),
        gf64::mul::<F>(gf64::mul::<F>(a, b), c),
        "associativity bits={} a={a:#x} b={b:#x} c={c:#x}",
        F::BITS
    );
    assert_eq!(
        gf64::mul::<F>(a, b ^ c),
        gf64::mul::<F>(a, b) ^ gf64::mul::<F>(a, c),
        "distributivity bits={} a={a:#x} b={b:#x} c={c:#x}",
        F::BITS
    );
    assert_eq!(
        maps::trace::<F>(a ^ b),
        maps::trace::<F>(a) ^ maps::trace::<F>(b),
        "trace linearity bits={} a={a:#x} b={b:#x} c={c:#x}",
        F::BITS
    );
    assert_eq!(
        gf64::mul::<F>(a, 1),
        a,
        "multiplicative identity bits={} a={a:#x} b={b:#x} c={c:#x}",
        F::BITS
    );
    assert_eq!(
        gf64::mul::<F>(a, 0),
        0,
        "zero product bits={} a={a:#x} b={b:#x} c={c:#x}",
        F::BITS
    );
}

fn exhaustive_small<F: BinaryField>() {
    assert_eq!(
        maps::trace::<F>(1),
        u8::try_from(F::BITS % 2).unwrap(),
        "trace(1)=BITS mod 2"
    );
    for a in 0..=F::MASK {
        check_unary::<F>(a);
        for b in 0..=F::MASK {
            check_product::<F>(a, b);
            for c in 0..=F::MASK {
                check_laws::<F>(a, b, c);
            }
        }
    }
}

#[test]
fn gf4_exhaustive() {
    exhaustive_small::<Gf4>();
}

#[test]
fn gf16_exhaustive() {
    exhaustive_small::<Gf16>();
}

#[test]
fn gf256_products_and_maps() {
    assert_eq!(maps::trace::<Gf256>(1), 0, "GF256 trace(1)");
    for a in 0..=Gf256::MASK {
        check_unary::<Gf256>(a);
        for b in 0..=Gf256::MASK {
            check_product::<Gf256>(a, b);
        }
    }
    corpus_laws::<Gf256>();
}

fn corpus_laws<F: BinaryField>() {
    let mut state = SEED;
    for _ in 0..4096 {
        let a = next(&mut state) & F::MASK;
        let b = next(&mut state) & F::MASK;
        let c = next(&mut state) & F::MASK;
        check_product::<F>(a, b);
        check_laws::<F>(a, b, c);
    }
}

#[test]
fn gf65536_unary_and_pairs() {
    assert_eq!(maps::trace::<Gf65536>(1), 0, "GF65536 trace(1)");
    for a in 0..=Gf65536::MASK {
        check_unary::<Gf65536>(a);
    }
    corpus_laws::<Gf65536>();
    let mut state = SEED;
    for _ in 0..16384 {
        check_product::<Gf65536>(
            next(&mut state) & Gf65536::MASK,
            next(&mut state) & Gf65536::MASK,
        );
    }
}

#[test]
fn gf64_maps_and_laws() {
    assert_eq!(maps::trace::<Gf64>(1), 0, "GF64 trace(1)");
    for bit in 0..64 {
        check_unary::<Gf64>(1 << bit);
    }
    for a in [0, 1, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555] {
        check_unary::<Gf64>(a);
    }
    let mut state = SEED;
    for _ in 0..2048 {
        check_unary::<Gf64>(next(&mut state));
    }
    corpus_laws::<Gf64>();
}

fn regenerate_quadratic<F: BinaryField>() -> Vec<u64> {
    let bits = usize::try_from(F::BITS).unwrap();
    let columns: Vec<_> = (0..bits)
        .map(|i| {
            let basis = 1 << i;
            reference::mul::<F>(basis, basis) ^ basis
        })
        .collect();
    let mut left: Vec<u64> = (0..bits)
        .map(|row| {
            columns
                .iter()
                .enumerate()
                .fold(0, |word, (col, value)| word | (((value >> row) & 1) << col))
        })
        .collect();
    let mut right: Vec<u64> = (0..bits).map(|row| 1 << row).collect();
    let mut pivots = Vec::new();
    for column in 0..bits {
        let rank = pivots.len();
        let Some(pivot) = (rank..bits).find(|&row| left[row] & (1 << column) != 0) else {
            continue;
        };
        left.swap(rank, pivot);
        right.swap(rank, pivot);
        for row in 0..bits {
            if row != rank && left[row] & (1 << column) != 0 {
                left[row] ^= left[rank];
                right[row] ^= right[rank];
            }
        }
        pivots.push(column);
    }
    assert_eq!(
        pivots,
        (1..bits).collect::<Vec<_>>(),
        "Q has only the constant-coordinate kernel"
    );
    let mut result = vec![0; bits];
    for (row, &column) in pivots.iter().enumerate() {
        assert_eq!(left[row], 1 << column, "reduced pivot row");
        result[column] = right[row];
    }
    result
}

#[test]
fn quadratic_constants() {
    fn check<F: BinaryField>() {
        assert_eq!(
            maps::quadratic_rows::<F>(),
            regenerate_quadratic::<F>(),
            "checked-in quadratic matrix"
        );
    }
    check::<Gf4>();
    check::<Gf16>();
    check::<Gf256>();
    check::<Gf65536>();
    check::<Gf64>();
}
