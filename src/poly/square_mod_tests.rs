//! Production mode: square-mod inside one charged row's root traversal.
#![forbid(unsafe_code)]

use {
    super::{Dense, Polynomial},
    crate::{
        backend::{contract::BulkKernels, portable::Portable},
        field::{BinaryField, Gf64, reference, tiny::Gf256},
        types::RawProduct,
    },
};

const GUARD: u64 = 0xdead_beef_cafe_1234;
const RAW_GUARD: RawProduct = RawProduct {
    lo: GUARD,
    hi: !GUARD,
};

fn next(seed: &mut u64) -> u64 {
    *seed ^= *seed << 13;
    *seed ^= *seed >> 7;
    *seed ^= *seed << 17;
    *seed
}

// Independent bit-serial squaring and long division; never uses the reducer table.
fn reference_square_mod<F: BinaryField>(a: &[u64], modulus: &[u64]) -> Vec<u64> {
    let degree = modulus.len() - 1;
    let mut remainder = vec![0; 2 * degree];
    for (i, &word) in a.iter().enumerate() {
        remainder[2 * i] = reference::mul::<F>(word, word);
    }
    for top in (degree..remainder.len()).rev() {
        let scale = remainder[top];
        for (i, &word) in modulus.iter().enumerate() {
            remainder[top - degree + i] ^= reference::mul::<F>(scale, word);
        }
    }
    remainder.truncate(degree);
    remainder
}

fn check<F: BinaryField, K: BulkKernels<F>>() -> usize {
    let mut seed = 0x675d_2239_7785_1231;
    let mut cases = 0;
    // All root-factor degrees and every input length, hence every coefficient
    // tail, including empty inputs, odd/even degrees and exact vector blocks.
    for degree in 3..=89 {
        let mut modulus: Vec<_> = (0..degree).map(|_| next(&mut seed) & F::MASK).collect();
        modulus.push(1);
        let mut table = vec![0; degree * (degree / 2)];
        let mut work = vec![0; 4 * (degree + 1)];
        <Dense as Polynomial<F, Portable>>::prepare_square_table(&modulus, &mut table, &mut work);
        for len in 0..=degree {
            let mut a: Vec<_> = (0..len).map(|_| next(&mut seed) & F::MASK).collect();
            // Exercise sparse, zero, unit and top-bit coefficients as well as
            // full-width random products, retaining a canonical nonempty input.
            for (i, word) in a.iter_mut().enumerate() {
                match i % 8 {
                    0 => *word = 0,
                    1 => *word = 1,
                    2 => *word = 1 << (F::BITS - 1),
                    _ => (),
                }
            }
            if let Some(last) = a.last_mut() {
                *last |= 1;
            }
            let expected = reference_square_mod::<F>(&a, &modulus);
            let expected_len = expected
                .iter()
                .rposition(|&word| word != 0)
                .map_or(0, |i| i + 1);
            for extra in [0, 8] {
                // Deliberately unaligned, dirty storage, exact and oversized
                // admitted buffers, guards on both sides of both mutable slices.
                let mut dst = vec![GUARD; degree + extra + 2];
                let raw_len = 2 * degree + 1;
                let mut raw = vec![RAW_GUARD; raw_len + extra + 2];
                let got_len = <Dense as Polynomial<F, K>>::square_mod_into(
                    &a,
                    &modulus,
                    &table,
                    &mut dst[1..degree + extra + 1],
                    &mut raw[1..raw_len + extra + 1],
                );
                assert_eq!(
                    &dst[1..=degree],
                    expected,
                    "square-mod bits={} d={degree} n={len}",
                    F::BITS
                );
                assert_eq!(
                    got_len, expected_len,
                    "normalized length d={degree} n={len}"
                );
                assert_eq!(dst[0], GUARD, "leading coefficient guard");
                assert!(
                    dst[degree + 1..].iter().all(|&word| word == GUARD),
                    "coefficient tail d={degree}"
                );
                assert_eq!(raw[0], RAW_GUARD, "leading scratch guard");
                assert!(
                    raw[raw_len + 1..].iter().all(|&word| word == RAW_GUARD),
                    "scratch tail d={degree}"
                );
                cases += 1;
            }
        }
    }
    cases
}

#[test]
fn square_mod_matches_bit_serial_all_decoder_degrees_and_tails() {
    let cases = check::<Gf64, Portable>() + check::<Gf256, Portable>();
    #[cfg(target_arch = "x86_64")]
    let cases = cases + check_x86_backends();
    eprintln!("SQUARE_MOD_BIT_SERIAL cases={cases}");
}

#[cfg(target_arch = "x86_64")]
fn check_x86_backends() -> usize {
    use crate::{
        backend::{detect, x86_pclmul::Pclmul, x86_vpclmul512::Vpclmul512},
        types::{BackendId, BackendRequest},
    };
    let mut cases = 0;
    if detect::resolve(BackendRequest::Force(BackendId::Pclmul)).is_ok() {
        cases += check::<Gf64, Pclmul>();
    }
    if detect::resolve(BackendRequest::Force(BackendId::Vpclmul512)).is_ok() {
        cases += check::<Gf64, Vpclmul512>() + check::<Gf256, Vpclmul512>();
    }
    cases
}
