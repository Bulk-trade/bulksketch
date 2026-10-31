//! Independent key-equation oracles over reference-field operations.
#![forbid(unsafe_code)]
use {
    super::bm,
    crate::{
        backend::portable::Portable,
        field::{
            BinaryField, Gf64, reference,
            tiny::{Gf4, Gf16, Gf256, Gf65536},
        },
        types::{DecodeFailure, WorkMeter, WorkUnits},
    },
};

pub(super) fn inverse<F: BinaryField>(a: u64) -> u64 {
    assert_ne!(a, 0);
    let mut result = 1;
    let mut power = a;
    let mut exponent = F::MASK - 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            result = reference::mul::<F>(result, power);
        }
        power = reference::mul::<F>(power, power);
        exponent >>= 1;
    }
    result
}
pub(super) fn trim(p: &mut Vec<u64>) {
    while p.last() == Some(&0) {
        p.pop();
    }
}
pub(super) fn multiply<F: BinaryField>(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut p = vec![0; a.len() + b.len()];
    for (i, &x) in a.iter().enumerate() {
        for (j, &y) in b.iter().enumerate() {
            p[i + j] ^= reference::mul::<F>(x, y);
        }
    }
    trim(&mut p);
    p
}
pub(super) fn divide<F: BinaryField>(a: &[u64], b: &[u64]) -> (Vec<u64>, Vec<u64>) {
    let mut r = a.to_vec();
    let mut q = vec![0; a.len()];
    let inv = inverse::<F>(*b.last().unwrap());
    while r.len() >= b.len() {
        let shift = r.len() - b.len();
        let scale = reference::mul::<F>(*r.last().unwrap(), inv);
        q[shift] = scale;
        for (i, &c) in b.iter().enumerate() {
            r[shift + i] ^= reference::mul::<F>(scale, c);
        }
        trim(&mut r);
    }
    trim(&mut q);
    (q, r)
}
pub(super) fn syndromes<F: BinaryField>(roots: &[u64], c: usize) -> Vec<u64> {
    let mut s = vec![0; 2 * c + 1];
    for &root in roots {
        let mut p = root;
        for value in &mut s[1..] {
            *value ^= p;
            p = reference::mul::<F>(p, root);
        }
    }
    s
}
fn reconstruct<F: BinaryField>(odd: &[u64]) -> Vec<u64> {
    let mut s = vec![0; 2 * odd.len() + 1];
    for i in 1..s.len() {
        s[i] = if i % 2 == 1 {
            odd[i / 2]
        } else {
            reference::mul::<F>(s[i / 2], s[i / 2])
        };
    }
    s
}
fn generic<F: BinaryField>(s: &[u64]) -> (usize, Vec<u64>) {
    let mut c = vec![1];
    let mut b = c.clone();
    let (mut l, mut shift, mut old) = (0, 1, 1);
    for n in 0..s.len() - 1 {
        let mut delta = s[n + 1];
        for i in 1..c.len() {
            delta ^= reference::mul::<F>(c[i], s[n + 1 - i]);
        }
        if delta == 0 {
            shift += 1;
            continue;
        }
        let saved = c.clone();
        let scale = reference::mul::<F>(delta, inverse::<F>(old));
        c.resize(c.len().max(b.len() + shift), 0);
        for (i, &v) in b.iter().enumerate() {
            c[i + shift] ^= reference::mul::<F>(v, scale);
        }
        trim(&mut c);
        if 2 * l <= n {
            l = n + 1 - l;
            b = saved;
            old = delta;
            shift = 1;
        } else {
            shift += 1;
        }
    }
    c.resize(l + 1, 0);
    c.reverse();
    (l, c)
}
fn euclid<F: BinaryField>(syndromes: &[u64]) -> Option<Vec<u64>> {
    let capacity = (syndromes.len() - 1) / 2;
    let mut left = vec![0; 2 * capacity + 1];
    left[2 * capacity] = 1;
    let mut right = syndromes[1..].to_vec();
    trim(&mut right);
    let (mut ta, mut tb) = (vec![], vec![1]);
    while right.len() > capacity {
        let (quotient, remainder) = divide::<F>(&left, &right);
        let mut connection = multiply::<F>(&quotient, &tb);
        connection.resize(connection.len().max(ta.len()), 0);
        for (i, &v) in ta.iter().enumerate() {
            connection[i] ^= v;
        }
        trim(&mut connection);
        left = right;
        right = remainder;
        ta = tb;
        tb = connection;
    }
    if tb.first().copied().unwrap_or(0) == 0 {
        return None;
    }
    let inv = inverse::<F>(tb[0]);
    for v in &mut tb {
        *v = reference::mul::<F>(*v, inv);
    }
    tb.reverse();
    Some(tb)
}
fn check<F: BinaryField>(odd: &[u64]) {
    let s = reconstruct::<F>(odd);
    let (degree, expected) = generic::<F>(&s);
    let c = odd.len();
    for budget in 0..=c {
        let mut memory = vec![F::MASK; 4 * (c + 1)];
        let before = memory.clone();
        let actual = bm::locator::<F, Portable>(
            &s,
            c,
            budget,
            &mut memory,
            &mut WorkMeter::new(WorkUnits(u64::MAX)),
        )
        .unwrap();
        if degree > budget {
            assert_eq!(
                actual,
                Err(DecodeFailure::DegreeExceedsBudget),
                "budget bits={} odd={odd:?} budget={budget}",
                F::BITS
            );
        } else if expected.first() == Some(&0) {
            assert_eq!(actual, Err(DecodeFailure::InvalidLocator));
        } else {
            assert_eq!(actual, Ok(degree), "degree bits={} odd={odd:?}", F::BITS);
            assert_eq!(
                &memory[..=degree],
                expected,
                "normalized reciprocal bits={} odd={odd:?}",
                F::BITS
            );
            assert_eq!(memory[degree], 1, "monic locator");
        }
        for block in 0..4 {
            assert_eq!(
                &memory[block * (c + 1) + budget + 1..(block + 1) * (c + 1)],
                &before[block * (c + 1) + budget + 1..(block + 1) * (c + 1)],
                "no out-of-budget writes"
            );
        }
    }
    if degree <= c && expected.first() != Some(&0) {
        assert_eq!(
            euclid::<F>(&s),
            Some(expected),
            "partial Euclid bits={} odd={odd:?}",
            F::BITS
        );
    }
}
fn arbitrary_corpus<F: BinaryField>() {
    let mut seed = 0x534b_4e43_4c34_0001u64;
    for c in [1, 2, 3, 4, 8, 18] {
        for _ in 0..24 {
            let odd = (0..c)
                .map(|_| {
                    seed ^= seed << 13;
                    seed ^= seed >> 7;
                    seed ^= seed << 17;
                    seed & F::MASK
                })
                .collect::<Vec<_>>();
            check::<F>(&odd);
        }
    }
}
#[test]
fn binary_bm_matches_independent_oracles() {
    let powers = syndromes::<Gf16>(&[1, 2, 3], 4);
    let odd = powers.into_iter().skip(1).step_by(2).collect::<Vec<_>>();
    check::<Gf16>(&odd);
    for c in 1..=4 {
        for mut code in 0..4usize.pow(u32::try_from(c).unwrap()) {
            let mut odd = vec![0; c];
            for v in &mut odd {
                *v = u64::try_from(code % 4).unwrap();
                code /= 4;
            }
            check::<Gf4>(&odd);
        }
    }
    for c in 1..=3 {
        for mut code in 0..16usize.pow(u32::try_from(c).unwrap()) {
            let mut odd = vec![0; c];
            for v in &mut odd {
                *v = u64::try_from(code % 16).unwrap();
                code /= 16;
            }
            check::<Gf16>(&odd);
        }
    }

    arbitrary_corpus::<Gf256>();
    arbitrary_corpus::<Gf65536>();
    arbitrary_corpus::<Gf64>();
}

// General BM fallback, every degree through each production capacity. Expected
// locators are products of (X+root) using only the bit-serial reference field.
#[test]
fn inversion_free_bm_matches_bit_serial_locators() {
    use crate::backend::contract::BulkKernels;
    #[cfg(target_arch = "x86_64")]
    use crate::{
        backend::detect,
        types::{BackendId, BackendRequest},
    };
    fn compare<K: BulkKernels<Gf64>>(s: &[u64], c: usize, d: usize, expected: &[u64]) {
        let mut buffers = vec![u64::MAX; 4 * (c + 1)];
        let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
        assert_eq!(
            bm::locator::<Gf64, K>(s, c, c, &mut buffers, &mut meter).unwrap(),
            Ok(d)
        );
        assert_eq!(
            &buffers[..=d],
            expected,
            "bit-exact monic locator c={c} d={d}"
        );
        let cost =
            super::work::WorkScheduleV1::cost(super::work::Charge::BmStep { budget: c }).unwrap();
        assert_eq!(
            meter.used().0,
            cost.0 * (2 * c) as u64,
            "unchanged BM-step charge points"
        );
    }
    let mut cases = 0;
    for c in [18, 72, 89] {
        for degree in 0..=c {
            let roots: Vec<_> = (0..degree)
                .map(|i| ((i as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15)).rotate_left(11))
                .collect();
            let s = syndromes::<Gf64>(&roots, c);
            let expected = roots
                .iter()
                .fold(vec![1], |p, &root| multiply::<Gf64>(&p, &[root, 1]));
            compare::<Portable>(&s, c, degree, &expected);
            #[cfg(target_arch = "x86_64")]
            {
                if detect::resolve(BackendRequest::Force(BackendId::Pclmul)).is_ok() {
                    compare::<crate::backend::x86_pclmul::Pclmul>(&s, c, degree, &expected);
                }
                if detect::resolve(BackendRequest::Force(BackendId::Vpclmul512)).is_ok() {
                    compare::<crate::backend::x86_vpclmul512::Vpclmul512>(&s, c, degree, &expected);
                }
            }
            cases += 1;
        }
    }
    println!("P4_BM_LOCATORS independent_cases={cases} exact_locator_and_work=true");
}
