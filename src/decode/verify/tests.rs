//! Production mode: complete rebuilt verification of a decoded GF64 row,
//! including both selected and unselected degrees and every stored odd word.
#![forbid(unsafe_code)]

use {
    super::{ProductCounts, product_counts, rebuilt_lfsr, use_rebuilt_lfsr},
    crate::{
        backend::{contract::BulkKernels, portable::Portable},
        field::{Gf64, reference},
    },
};

fn independent_odd(roots: &[u64], capacity: usize) -> Vec<u64> {
    let mut odd = vec![0; capacity];
    for &root in roots {
        let step = reference::mul::<Gf64>(root, root);
        let mut power = root;
        for (index, word) in odd.iter_mut().enumerate() {
            *word ^= power;
            if index + 1 < capacity {
                power = reference::mul::<Gf64>(power, step);
            }
        }
    }
    odd
}

fn roots(degree: usize, family: usize) -> Vec<u64> {
    (1..=degree)
        .map(|index| match family {
            // Odd multiplication is a permutation modulo 2^64.
            0 => (index as u64).wrapping_mul(0xd6e8_feb8_6659_fd93),
            // Leading-zero row IDs, with the same bucket routing suffix.
            1 => ((index as u64) << 4) | 3,
            // An affine coset with a rank-deficient difference hull.
            _ => 0xfedc_ba98_7654_0000 ^ (index as u64),
        })
        .collect()
}

fn all_words<K: BulkKernels<Gf64>>() -> (usize, usize) {
    let mut valid = 0;
    let mut corruptions = 0;
    for capacity in [18, 89] {
        for degree in (3..=capacity).chain(0..3) {
            for family in 0..3 {
                let roots = roots(degree, family);
                let mut odd = independent_odd(&roots, capacity);
                let mut coefficients = vec![u64::MAX; degree + 3];
                let mut expected = vec![u64::MAX; capacity + 2];
                assert!(
                    rebuilt_lfsr::<Gf64, K>(
                        &roots,
                        &odd,
                        &mut coefficients[1..=degree + 1],
                        &mut expected[1..=capacity],
                    ),
                    "rebuilt LFSR rejected valid row c{capacity} d{degree} family{family}"
                );
                assert_eq!(
                    (coefficients[0], coefficients[degree + 2]),
                    (u64::MAX, u64::MAX)
                );
                assert_eq!((expected[0], expected[capacity + 1]), (u64::MAX, u64::MAX));
                valid += 1;
                for word in 0..capacity {
                    odd[word] ^= 1_u64 << (word % 64);
                    assert!(
                        !rebuilt_lfsr::<Gf64, K>(
                            &roots,
                            &odd,
                            &mut coefficients[1..=degree + 1],
                            &mut expected[1..=capacity],
                        ),
                        "rebuilt LFSR accepted corruption c{capacity} d{degree} family{family} \
                         word{word}"
                    );
                    odd[word] ^= 1_u64 << (word % 64);
                    corruptions += 1;
                }
                // The same scratch must rebuild from the new roots; neither BM
                // coefficients nor the previous verified row may certify them.
                if degree > 0 {
                    let mut wrong_roots = roots.clone();
                    wrong_roots[degree - 1] ^= 1_u64 << 63;
                    assert!(
                        !rebuilt_lfsr::<Gf64, K>(
                            &wrong_roots,
                            &odd,
                            &mut coefficients[1..=degree + 1],
                            &mut expected[1..=capacity],
                        ),
                        "rebuilt LFSR trusted previous roots c{capacity} d{degree} family{family}"
                    );
                }
            }
        }
    }
    (valid, corruptions)
}

#[test]
fn rebuilt_lfsr_checks_every_word_all_backends() {
    let (valid, corruptions) = all_words::<Portable>();
    #[cfg(target_arch = "x86_64")]
    let (valid, corruptions) = {
        let (mut valid, mut corruptions) = (valid, corruptions);
        use crate::{
            backend::detect,
            types::{BackendId, BackendRequest},
        };
        if detect::resolve(BackendRequest::Force(BackendId::Pclmul)).is_ok() {
            let (v, c) = all_words::<crate::backend::x86_pclmul::Pclmul>();
            valid += v;
            corruptions += c;
        }
        if detect::resolve(BackendRequest::Force(BackendId::Vpclmul512)).is_ok() {
            let (v, c) = all_words::<crate::backend::x86_vpclmul512::Vpclmul512>();
            valid += v;
            corruptions += c;
        }
        (valid, corruptions)
    };
    eprintln!("ROOTMIX_LFSR valid={valid} independent_word_corruptions={corruptions}");
}

/// Count the actual padded kernel loops independently of the selector's closed
/// forms. Counts include scalar coefficient squares and delayed reductions.
fn counted_products(degree: usize, capacity: usize) -> (ProductCounts, ProductCounts) {
    let mut current = ProductCounts {
        raw: 0,
        including_reduction: 0,
    };
    let mut prefix = current;
    for start in (0..degree).step_by(32) {
        let remaining = (degree - start).min(32);
        let (vectors, per_vector) = match remaining {
            1..=8 => (1, 6),
            9..=16 => (2, 6),
            _ => (4, 2),
        };
        for _ in 0..capacity {
            current.raw += 2 * vectors;
            current.including_reduction += per_vector * vectors;
        }
        for _ in 0..degree {
            prefix.raw += 2 * vectors;
            prefix.including_reduction += per_vector * vectors;
        }
    }
    let mut rebuilt = prefix;
    for inserted in 1..=degree {
        let mut end = inserted + 1;
        while end > 1 {
            rebuilt.raw += 2;
            rebuilt.including_reduction += 6;
            end = end.saturating_sub(8).max(1);
        }
    }
    for _ in 0..degree {
        rebuilt.raw += 1;
        rebuilt.including_reduction += 3;
    }
    for _ in (degree..capacity).step_by(8) {
        for _ in 0..degree {
            rebuilt.raw += 2;
            rebuilt.including_reduction += 2;
        }
        rebuilt.including_reduction += 4;
    }
    (current, rebuilt)
}

#[test]
fn lfsr_dispatch_follows_instruction_counts() {
    for capacity in [1, 2, 18, 32, 89, 288] {
        for degree in 0..=capacity {
            let (current, rebuilt) = counted_products(degree, capacity);
            assert_eq!(product_counts(degree, capacity), Some((current, rebuilt)));
            let expected = degree > 2
                && rebuilt.raw <= current.raw
                && rebuilt.including_reduction <= current.including_reduction
                && rebuilt != current;
            assert_eq!(
                use_rebuilt_lfsr(degree, capacity),
                expected,
                "LFSR dispatch disagrees with counted kernels c{capacity} d{degree}"
            );
        }
    }
    assert!(!use_rebuilt_lfsr(3, 2));
    assert!(!use_rebuilt_lfsr(3, usize::from(u16::MAX) + 1));
}
