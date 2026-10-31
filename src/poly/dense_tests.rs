#![forbid(unsafe_code)]

use {
    super::{Dense, Polynomial, RawProduct},
    crate::{
        backend::portable::Portable,
        field::{
            BinaryField, Gf64, reference,
            tiny::{Gf4, Gf16, Gf256, Gf65536},
        },
    },
};

const SEED: u64 = 0x534b_4e43_4c33_0001;
const GARBAGE: u64 = 0xdead_beef_cafe_1234;
const RAW_GARBAGE: RawProduct = RawProduct {
    lo: GARBAGE,
    hi: !GARBAGE,
};

struct Guard<T> {
    words: Vec<T>,
    size: usize,
    oversized: bool,
}
impl<T: Copy + PartialEq + std::fmt::Debug> Guard<T> {
    fn new(size: usize, value: T, oversized: bool) -> Self {
        Self {
            words: vec![value; size + 2],
            size,
            oversized,
        }
    }
    fn buffer(&mut self) -> &mut [T] {
        let end = if self.oversized {
            self.size + 2
        } else {
            self.size + 1
        };
        &mut self.words[1..end]
    }
    fn data(&self) -> &[T] {
        &self.words[1..=self.size]
    }
    fn check(&self, value: T) {
        assert_eq!(self.words[0], value, "leading storage guard");
        assert_eq!(self.words[self.size + 1], value, "trailing storage guard");
    }
}

fn normalize(mut p: Vec<u64>) -> Vec<u64> {
    while p.last() == Some(&0) {
        p.pop();
    }
    p
}

fn product<F: BinaryField>(a: &[u64], b: &[u64]) -> Vec<u64> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut out = vec![0; a.len() + b.len() - 1];
    for (i, &left) in a.iter().enumerate() {
        for (j, &right) in b.iter().enumerate() {
            out[i + j] ^= reference::mul::<F>(left, right);
        }
    }
    normalize(out)
}

fn power<F: BinaryField>(mut base: u64, mut exponent: u64) -> u64 {
    let mut out = 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            out = reference::mul::<F>(out, base);
        }
        base = reference::mul::<F>(base, base);
        exponent >>= 1;
    }
    out
}

fn divide<F: BinaryField>(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    assert!(!b.is_empty());
    let inverse = power::<F>(b[b.len() - 1], F::MASK - 1);
    let mut rem = a.to_vec();
    let mut q = vec![0; a.len()];
    while !rem.is_empty() && rem.len() >= b.len() {
        let offset = rem.len() - b.len();
        let scale = reference::mul::<F>(rem[rem.len() - 1], inverse);
        q[offset] = scale;
        for (i, &coefficient) in b.iter().enumerate() {
            rem[offset + i] ^= reference::mul::<F>(coefficient, scale);
        }
        rem = normalize(rem);
    }
    (normalize(q), rem)
}

fn gcd<F: BinaryField>(a: &[u64], b: &[u64]) -> Vec<u64> {
    let (mut left, mut right) = (a.to_vec(), b.to_vec());
    while !right.is_empty() {
        let (_, rem) = divide::<F>(&left, &right);
        left = right;
        right = rem;
    }
    if let Some(&leading) = left.last() {
        let inverse = power::<F>(leading, F::MASK - 1);
        for coefficient in &mut left {
            *coefficient = reference::mul::<F>(*coefficient, inverse);
        }
    }
    left
}

fn evaluate<F: BinaryField>(coefficients: &[u64], point: u64) -> u64 {
    coefficients
        .iter()
        .enumerate()
        .fold(0, |sum, (i, &coefficient)| {
            sum ^ reference::mul::<F>(coefficient, power::<F>(point, u64::try_from(i).unwrap()))
        })
}

fn next(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut word = *state;
    word = (word ^ (word >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    word = (word ^ (word >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    word ^ (word >> 31)
}

fn corpus<F: BinaryField>() -> Vec<Vec<u64>> {
    let mut state = SEED;
    let mut out = vec![
        vec![],
        vec![1],
        vec![2],
        vec![0, 1],
        vec![1, 1],
        vec![1, 0, 1],
        vec![F::MASK; 4],
    ];
    for len in [1, 2, 3, 4, 5, 8, 17, 33, 65] {
        for _ in 0..3 {
            out.push(normalize(
                (0..len).map(|_| next(&mut state) & F::MASK).collect(),
            ));
        }
    }
    out
}

fn enumerate<F: BinaryField>(words: u32) -> Vec<Vec<u64>> {
    let order = F::MASK + 1;
    (0..order.pow(words))
        .map(|mut code| {
            normalize(
                (0..words)
                    .map(|_| {
                        let digit = code % order;
                        code /= order;
                        digit
                    })
                    .collect(),
            )
        })
        .collect()
}

fn check_product<F: BinaryField>(a: &[u64], b: &[u64]) {
    let expected = product::<F>(a, b);
    let size = if a.is_empty() || b.is_empty() {
        0
    } else {
        a.len() + b.len()
    };
    for oversized in [false, true] {
        let mut dst = Guard::new(size, GARBAGE, oversized);
        let mut raw = Guard::new(size, RAW_GARBAGE, oversized);
        let len = <Dense as Polynomial<F, Portable>>::mul_into(a, b, dst.buffer(), raw.buffer());
        assert_eq!(
            &dst.data()[..len],
            expected,
            "product bits={} a={a:?} b={b:?}",
            F::BITS
        );
        dst.check(GARBAGE);
        raw.check(RAW_GARBAGE);
    }
}

fn check_square<F: BinaryField>(a: &[u64]) {
    for oversized in [false, true] {
        let size = 2 * a.len();
        let mut dst = Guard::new(size, GARBAGE, oversized);
        let mut raw = Guard::new(size, RAW_GARBAGE, oversized);
        let len = <Dense as Polynomial<F, Portable>>::square_into(a, dst.buffer(), raw.buffer());
        assert_eq!(
            &dst.data()[..len],
            product::<F>(a, a),
            "square bits={} a={a:?}",
            F::BITS
        );
        dst.check(GARBAGE);
        raw.check(RAW_GARBAGE);
    }
}

fn products<F: BinaryField>(polynomials: &[Vec<u64>]) {
    for a in polynomials {
        check_square::<F>(a);
        for b in polynomials {
            check_product::<F>(a, b);
        }
    }
}

#[test]
fn products_match_reference() {
    products::<Gf64>(&corpus::<Gf64>());
    products::<Gf4>(&enumerate::<Gf4>(3));
    products::<Gf16>(&enumerate::<Gf16>(2));
    products::<Gf256>(&corpus::<Gf256>());
    products::<Gf65536>(&corpus::<Gf65536>());
}

fn check_division<F: BinaryField>(a: &[u64], b: &[u64]) {
    let (expected_q, expected_rem) = divide::<F>(a, b);
    for oversized in [false, true] {
        let size = a.len() + 1;
        let mut q = Guard::new(size, GARBAGE, oversized);
        let mut rem = Guard::new(size, GARBAGE, oversized);
        let mut raw = Guard::new(size, RAW_GARBAGE, oversized);
        let (qn, rn) = <Dense as Polynomial<F, Portable>>::div_rem_into(
            a,
            b,
            q.buffer(),
            rem.buffer(),
            raw.buffer(),
        );
        assert_eq!(
            &q.data()[..qn],
            expected_q,
            "quotient bits={} a={a:?} b={b:?}",
            F::BITS
        );
        assert_eq!(
            &rem.data()[..rn],
            expected_rem,
            "remainder bits={} a={a:?} b={b:?}",
            F::BITS
        );
        assert!(
            rn < b.len(),
            "remainder degree bits={} a={a:?} b={b:?}",
            F::BITS
        );
        let mut reconstructed = product::<F>(&q.data()[..qn], b);
        reconstructed.resize(reconstructed.len().max(rn), 0);
        for (slot, &word) in reconstructed.iter_mut().zip(&rem.data()[..rn]) {
            *slot ^= word;
        }
        assert_eq!(
            normalize(reconstructed),
            a,
            "division identity bits={} a={a:?} b={b:?}",
            F::BITS
        );
        q.check(GARBAGE);
        rem.check(GARBAGE);
        raw.check(RAW_GARBAGE);
    }
}

fn divisions<F: BinaryField>(polynomials: &[Vec<u64>]) {
    for a in polynomials {
        for b in polynomials.iter().filter(|p| !p.is_empty()) {
            check_division::<F>(a, b);
        }
    }
}

#[test]
fn division_matches_reference() {
    divisions::<Gf64>(&corpus::<Gf64>());
    divisions::<Gf4>(&enumerate::<Gf4>(3));
    divisions::<Gf16>(&enumerate::<Gf16>(2));
    divisions::<Gf256>(&corpus::<Gf256>());
    divisions::<Gf65536>(&corpus::<Gf65536>());
}

fn exact_divisions<F: BinaryField>() {
    let polynomials = corpus::<F>();
    for a in &polynomials {
        for b in polynomials.iter().filter(|p| !p.is_empty()) {
            for dividend in [a.clone(), product::<F>(a, b)] {
                let (expected_q, expected_rem) = divide::<F>(&dividend, b);
                for oversized in [false, true] {
                    let size = dividend.len() + 1;
                    let mut q = Guard::new(size, GARBAGE, oversized);
                    let mut rem = Guard::new(size, GARBAGE, oversized);
                    let mut raw = Guard::new(size, RAW_GARBAGE, oversized);
                    let result = <Dense as Polynomial<F, Portable>>::exact_divide_into(
                        &dividend,
                        b,
                        q.buffer(),
                        rem.buffer(),
                        raw.buffer(),
                    );
                    if expected_rem.is_empty() {
                        assert_eq!(
                            result,
                            Some(expected_q.len()),
                            "exact quotient length bits={} a={dividend:?} b={b:?}",
                            F::BITS
                        );
                        assert_eq!(
                            &q.data()[..expected_q.len()],
                            expected_q,
                            "exact quotient bits={} a={dividend:?} b={b:?}",
                            F::BITS
                        );
                    } else {
                        assert_eq!(
                            result,
                            None,
                            "inexact division bits={} a={dividend:?} b={b:?}",
                            F::BITS
                        );
                        assert!(
                            q.data().iter().all(|&x| x == 0),
                            "failed exact division clears quotient bits={} a={dividend:?} b={b:?}",
                            F::BITS
                        );
                    }
                    assert_eq!(
                        &rem.data()[..expected_rem.len()],
                        expected_rem,
                        "exact remainder bits={} a={dividend:?} b={b:?}",
                        F::BITS
                    );
                    assert!(
                        rem.data()[expected_rem.len()..].iter().all(|&x| x == 0),
                        "remainder padding"
                    );
                    q.check(GARBAGE);
                    rem.check(GARBAGE);
                    raw.check(RAW_GARBAGE);
                }
            }
        }
    }
}

#[test]
fn exact_division_is_transactional() {
    exact_divisions::<Gf64>();
    exact_divisions::<Gf4>();
    exact_divisions::<Gf16>();
    exact_divisions::<Gf256>();
    exact_divisions::<Gf65536>();
}

fn evaluations<F: BinaryField>() {
    let mut state = SEED;
    let mut points = vec![0, 1, 2, F::MASK, 1_u64 << (F::BITS - 1)];
    points.extend((0..17).map(|_| next(&mut state) & F::MASK));
    for coefficients in corpus::<F>() {
        for count in 0..=points.len() {
            for oversized in [false, true] {
                let mut out = Guard::new(count, GARBAGE, oversized);
                // horner_many's fixed contract requires equal output/point dimensions.
                let len = out.size;
                <Dense as Polynomial<F, Portable>>::eval_many_into(
                    &coefficients,
                    &points[..count],
                    &mut out.buffer()[..len],
                );
                let expected: Vec<_> = points[..count]
                    .iter()
                    .map(|&p| evaluate::<F>(&coefficients, p))
                    .collect();
                assert_eq!(
                    out.data(),
                    expected,
                    "evaluation bits={} coefficients={coefficients:?} points={:?}",
                    F::BITS,
                    &points[..count]
                );
                out.check(GARBAGE);
            }
        }
    }
}

#[test]
fn evaluation_matches_power_sum() {
    evaluations::<Gf64>();
    evaluations::<Gf4>();
    evaluations::<Gf16>();
    evaluations::<Gf256>();
    evaluations::<Gf65536>();
}

#[test]
fn xor_extends_and_normalizes() {
    for oversized in [false, true] {
        let mut dst = Guard::new(9, GARBAGE, oversized);
        let mut len = <Dense as Polynomial<Gf64, Portable>>::xor_coefficient(dst.buffer(), 0, 8, 7);
        assert_eq!(len, 9, "extension length");
        assert_eq!(
            dst.data(),
            [0, 0, 0, 0, 0, 0, 0, 0, 7],
            "empty polynomial zero extension"
        );
        len = <Dense as Polynomial<Gf64, Portable>>::xor_coefficient(dst.buffer(), len, 1, 3);
        assert_eq!(len, 9, "low coefficient preserves high term");
        len = <Dense as Polynomial<Gf64, Portable>>::xor_coefficient(dst.buffer(), len, 8, 7);
        assert_eq!(len, 2, "leading cancellation normalizes");
        len = <Dense as Polynomial<Gf64, Portable>>::xor_coefficient(dst.buffer(), len, 1, 3);
        assert_eq!(len, 0, "complete cancellation normalizes to empty");
        len = <Dense as Polynomial<Gf64, Portable>>::xor_coefficient(dst.buffer(), len, 5, 0);
        assert_eq!(len, 0, "zero extension remains empty");
        dst.check(GARBAGE);
    }
}

fn gcds<F: BinaryField>(polynomials: &[Vec<u64>]) {
    for a in polynomials {
        for b in polynomials {
            for oversized in [false, true] {
                let size = a.len().max(b.len());
                let mut dst = Guard::new(size, GARBAGE, oversized);
                let mut work = Guard::new(4 * (size + 1), GARBAGE, oversized);
                let mut raw = Guard::new(2 * (size + 1), RAW_GARBAGE, oversized);
                let len = <Dense as Polynomial<F, Portable>>::monic_gcd_into(
                    a,
                    b,
                    dst.buffer(),
                    work.buffer(),
                    raw.buffer(),
                );
                let actual = &dst.data()[..len];
                assert_eq!(
                    actual,
                    gcd::<F>(a, b),
                    "monic gcd bits={} a={a:?} b={b:?}",
                    F::BITS
                );
                if len != 0 {
                    assert_eq!(
                        actual.last(),
                        Some(&1),
                        "gcd is monic bits={} a={a:?} b={b:?}",
                        F::BITS
                    );
                    assert!(
                        divide::<F>(a, actual).1.is_empty(),
                        "gcd divides left bits={} a={a:?} b={b:?}",
                        F::BITS
                    );
                    assert!(
                        divide::<F>(b, actual).1.is_empty(),
                        "gcd divides right bits={} a={a:?} b={b:?}",
                        F::BITS
                    );
                } else {
                    assert!(a.is_empty() && b.is_empty(), "only gcd(0,0) is zero");
                }
                dst.check(GARBAGE);
                work.check(GARBAGE);
                raw.check(RAW_GARBAGE);
            }
        }
    }
}

#[test]
fn gcd_matches_reference() {
    gcds::<Gf64>(&corpus::<Gf64>());
    gcds::<Gf4>(&enumerate::<Gf4>(3));
    gcds::<Gf16>(&enumerate::<Gf16>(2));
    gcds::<Gf256>(&corpus::<Gf256>());
    gcds::<Gf65536>(&corpus::<Gf65536>());
}

fn check_table<F: BinaryField>(modulus: &[u64], residues: &[Vec<u64>]) {
    let d = modulus.len() - 1;
    let size = d * (d / 2);
    for oversized in [false, true] {
        let mut table = Guard::new(size, GARBAGE, oversized);
        let mut work = Guard::new(4 * (d + 1), GARBAGE, oversized);
        <Dense as Polynomial<F, Portable>>::prepare_square_table(
            modulus,
            table.buffer(),
            work.buffer(),
        );
        for (row, i) in (d.div_ceil(2)..d).enumerate() {
            let mut monomial = vec![0; 2 * i + 1];
            monomial[2 * i] = 1;
            let mut expected = divide::<F>(&monomial, modulus).1;
            expected.resize(d, 0);
            assert_eq!(
                &table.data()[row * d..(row + 1) * d],
                expected,
                "square table row bits={} modulus={modulus:?} i={i}",
                F::BITS
            );
        }
        table.check(GARBAGE);
        work.check(GARBAGE);
        for a in residues {
            let mut dst = Guard::new(d, GARBAGE, oversized);
            let mut raw = Guard::new(2 * d + 1, RAW_GARBAGE, oversized);
            let len = <Dense as Polynomial<F, Portable>>::square_mod_into(
                a,
                modulus,
                table.data(),
                dst.buffer(),
                raw.buffer(),
            );
            assert_eq!(
                &dst.data()[..len],
                divide::<F>(&product::<F>(a, a), modulus).1,
                "square mod bits={} modulus={modulus:?} a={a:?}",
                F::BITS
            );
            dst.check(GARBAGE);
            raw.check(RAW_GARBAGE);
        }
    }
}

fn tables<F: BinaryField>() {
    let mut state = SEED;
    for d in [3, 4, 5, 8, 17, 32, 63, 64] {
        let mut modulus: Vec<_> = (0..d).map(|_| next(&mut state) & F::MASK).collect();
        modulus.push(1);
        let mut residues = vec![vec![], vec![1], vec![2], vec![F::MASK; d]];
        for i in 0..d {
            let mut a = vec![0; i + 1];
            a[i] = 2;
            residues.push(a);
        }
        for len in 1..=d {
            residues.push(normalize(
                (0..len).map(|_| next(&mut state) & F::MASK).collect(),
            ));
        }
        check_table::<F>(&modulus, &residues);
    }
}

#[test]
fn square_tables_match_square_then_divide() {
    assert_eq!(
        64 * 32 * std::mem::size_of::<u64>(),
        16 * 1024,
        "degree 64 table bytes"
    );
    tables::<Gf64>();
    tables::<Gf4>();
    tables::<Gf16>();
    tables::<Gf256>();
    tables::<Gf65536>();
    for mut modulus in enumerate::<Gf4>(3) {
        modulus.resize(3, 0);
        modulus.push(1);
        check_table::<Gf4>(&modulus, &enumerate::<Gf4>(3));
    }
    for constant in 0..16 {
        check_table::<Gf16>(&[constant, 0, 0, 1], &enumerate::<Gf16>(2));
    }
}

fn trace_fixture<F: BinaryField>() {
    let modulus = [1, 0, 0, 1];
    let mut table = [GARBAGE; 3];
    let mut work = [GARBAGE; 16];
    <Dense as Polynomial<F, Portable>>::prepare_square_table(&modulus, &mut table, &mut work);
    assert_eq!(table, [0, 1, 0], "X^4 mod (X^3+1) = X");
    let mut trace = [GARBAGE; 3];
    let mut len = <Dense as Polynomial<F, Portable>>::xor_coefficient(&mut trace, 0, 1, 1);
    let mut expected = vec![0, 1];
    let mut saw_zero = false;
    let mut extended_after_zero = false;
    // Four steps include an empty trace followed by square(0) and XOR into it.
    for step in 0..usize::try_from(F::BITS - 1).unwrap().max(4) {
        let mut squared = [GARBAGE; 3];
        let mut raw = [RAW_GARBAGE; 7];
        let square_len = <Dense as Polynomial<F, Portable>>::square_mod_into(
            &trace[..len],
            &modulus,
            &table,
            &mut squared,
            &mut raw,
        );
        if step == 3 {
            assert_eq!(square_len, 0, "zero trace must square to empty");
        }
        len = <Dense as Polynomial<F, Portable>>::xor_coefficient(&mut squared, square_len, 1, 1);
        if saw_zero && len != 0 {
            extended_after_zero = true;
        }
        saw_zero |= len == 0;
        expected = divide::<F>(&product::<F>(&expected, &expected), &modulus).1;
        expected.resize(expected.len().max(2), 0);
        expected[1] ^= 1;
        expected = normalize(expected);
        assert_eq!(
            &squared[..len],
            expected,
            "trace recurrence bits={} step={step}",
            F::BITS
        );
        trace = squared;
    }
    assert!(
        saw_zero && extended_after_zero,
        "trace reaches zero then re-extends bits={}",
        F::BITS
    );
}

#[test]
fn trace_zero_reextends() {
    trace_fixture::<Gf64>();
    trace_fixture::<Gf4>();
    trace_fixture::<Gf16>();
    trace_fixture::<Gf256>();
    trace_fixture::<Gf65536>();
}
