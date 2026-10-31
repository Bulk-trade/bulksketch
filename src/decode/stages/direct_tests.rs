//! DirectOne/DirectTwo production row driver, with an independent bit-serial oracle.
#![forbid(unsafe_code)]
use {
    super::*,
    crate::{
        backend::{contract::Arithmetic, portable::Portable},
        decode::row_tests::{Arena, Outcome, own},
        field::{Gf64, reference},
        types::{RawProduct, WorkUnits},
    },
};

#[derive(Clone, Copy)]
struct SingleId;
impl Arithmetic<Gf64> for SingleId {
    fn mul(a: u64, b: u64) -> u64 {
        <Portable as Arithmetic<Gf64>>::mul(a, b)
    }
    fn square(a: u64) -> u64 {
        <Portable as Arithmetic<Gf64>>::square(a)
    }
    fn frobenius(a: u64, p: u32) -> u64 {
        <Portable as Arithmetic<Gf64>>::frobenius(a, p)
    }
    fn inverse(a: u64) -> Option<u64> {
        <Portable as Arithmetic<Gf64>>::inverse(a)
    }
    fn trace(a: u64) -> u8 {
        <Portable as Arithmetic<Gf64>>::trace(a)
    }
    fn solve_quadratic(a: u64) -> Option<u64> {
        <Portable as Arithmetic<Gf64>>::solve_quadratic(a)
    }
    fn raw_mul(a: u64, b: u64) -> RawProduct {
        <Portable as Arithmetic<Gf64>>::raw_mul(a, b)
    }
    fn reduce(p: RawProduct) -> u64 {
        <Portable as Arithmetic<Gf64>>::reduce(p)
    }
    fn dot(a: &[u64], b: &[u64]) -> u64 {
        <Portable as Arithmetic<Gf64>>::dot(a, b)
    }
    fn scale_xor(a: &mut [u64], b: &[u64], s: u64) {
        <Portable as Arithmetic<Gf64>>::scale_xor(a, b, s);
    }
    fn square_slice(a: &mut [u64], b: &[u64]) {
        <Portable as Arithmetic<Gf64>>::square_slice(a, b);
    }
}
impl BulkKernels<Gf64> for SingleId {
    fn insert_nonzero(odd: &mut [u64], ids: &[u64]) {
        assert!(
            ids.len() <= 1,
            "tiny verification must use the single-ID kernel"
        );
        <Portable as BulkKernels<Gf64>>::insert_nonzero(odd, ids);
    }
    fn xor_assign(a: &mut [u64], b: &[u64]) {
        <Portable as BulkKernels<Gf64>>::xor_assign(a, b);
    }
    fn horner_many(c: &[u64], p: &[u64], out: &mut [u64]) {
        <Portable as BulkKernels<Gf64>>::horner_many(c, p, out);
    }
}
fn odd(roots: &[u64], c: usize) -> Vec<u64> {
    let mut words = vec![0; c];
    for &root in roots {
        let square = reference::mul::<Gf64>(root, root);
        let mut power = root;
        for word in &mut words {
            *word ^= power;
            power = reference::mul::<Gf64>(power, square);
        }
    }
    words
}
fn decode<K: BulkKernels<Gf64>>(words: &[u64], beta: usize) -> Outcome {
    let mut arena = Arena::new(words.len(), beta, u64::MAX);
    let mut workspace = arena.workspace();
    let mut row = <BinaryDecoder as RowDecoder<Gf64, K>>::begin(RowBudget {
        nonzero: beta,
        total: beta,
    });
    row.start_probes(words);
    let result = row
        .finish(
            RowInput {
                difference: words,
                candidates: &[],
            },
            &mut workspace,
            &mut WorkMeter::new(WorkUnits(u64::MAX)),
        )
        .unwrap();
    own(&result)
}
#[test]
fn tiny_verification_uses_single_id_calls() {
    for c in [18, 32, 72, 89] {
        for ids in [
            &[0x1234_5678_9abc_def0][..],
            &[0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210][..],
        ] {
            let mut expected = ids.to_vec();
            expected.sort_unstable();
            assert_eq!(
                decode::<SingleId>(&odd(ids, c), 2),
                Outcome::Decoded(expected)
            );
        }
    }
}
fn every_word<K: BulkKernels<Gf64>>() {
    for c in [18, 32, 72, 89] {
        for ids in [
            &[0x1234_5678_9abc_def0][..],
            &[0x1234_5678_9abc_def0, 0xfedc_ba98_7654_3210][..],
        ] {
            let words = odd(ids, c);
            let mut expected = ids.to_vec();
            expected.sort_unstable();
            assert_eq!(decode::<K>(&words, 2), Outcome::Decoded(expected.clone()));
            for index in 0..c {
                let mut bad = words.clone();
                bad[index] ^= 1;
                assert_ne!(
                    decode::<K>(&bad, 2),
                    Outcome::Decoded(expected.clone()),
                    "c={c} word={index}"
                );
            }
        }
    }
}
#[test]
fn tiny_verification_checks_every_word() {
    every_word::<Portable>();
    #[cfg(target_arch = "x86_64")]
    {
        use crate::backend::{x86_pclmul, x86_vpclmul512};
        if crate::backend::detect::resolve(crate::types::BackendRequest::Force(
            crate::types::BackendId::Pclmul,
        ))
        .is_ok()
        {
            every_word::<x86_pclmul::Pclmul>();
        }
        if crate::backend::detect::resolve(crate::types::BackendRequest::Force(
            crate::types::BackendId::Vpclmul512,
        ))
        .is_ok()
        {
            every_word::<x86_vpclmul512::Vpclmul512>();
        }
    }
}
