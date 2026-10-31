#![forbid(unsafe_code)]

use {
    super::{
        contract::{Arithmetic, BulkKernels},
        portable::Portable,
        x86_vpclmul512::{self as vector, Vpclmul512},
    },
    crate::{
        field::{Gf64, reference},
        types::RawProduct,
    },
};

fn mix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

#[test]
fn raw_products_and_reductions() {
    if !vector::available() {
        return;
    }
    for sample in 0..256 {
        let a = std::array::from_fn(|i| match sample {
            0 => u64::MAX,
            1..=64 => 1 << (sample - 1),
            _ => mix(sample * 8 + i as u64),
        });
        let b = std::array::from_fn(|i| match i {
            0 => 0,
            1 => 1,
            2 => 1 << 63,
            3 => u64::MAX,
            _ => mix(sample * 17 + i as u64),
        });
        let (lo, hi) = vector::test_products(&a, &b);
        for &word in &a {
            for power in 1..=7 {
                assert_eq!(
                    vector::test_frobenius(word, power),
                    <Portable as Arithmetic<Gf64>>::frobenius(word, u32::try_from(power).unwrap()),
                    "insertion Frobenius power={power}"
                );
            }
        }
        for i in 0..8 {
            assert_eq!(
                RawProduct {
                    lo: lo[i],
                    hi: hi[i]
                },
                reference::raw_mul::<Gf64>(a[i], b[i]),
                "raw lane {i} sample {sample}"
            );
        }
        for (lo, hi) in [(lo, hi), (a, b)] {
            let (shift, cl) = vector::test_reductions(&lo, &hi);
            for i in 0..8 {
                let expected = reference::reduce::<Gf64>(RawProduct {
                    lo: lo[i],
                    hi: hi[i],
                });
                assert_eq!(shift[i], expected, "shift reduction lane {i}");
                assert_eq!(cl[i], expected, "CL reduction lane {i}");
            }
        }
    }
}

#[test]
fn bulk_tails_and_unaligned_slices() {
    if !vector::available() {
        return;
    }
    let a: Vec<_> = (0..48).map(mix).collect();
    let b: Vec<_> = (48..96).map(mix).collect();
    for n in [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33] {
        for offset in 0..8 {
            let (a, b) = (&a[offset..offset + n], &b[7 - offset..7 - offset + n]);
            assert_eq!(
                <Vpclmul512 as Arithmetic<Gf64>>::dot(a, b),
                <Portable as Arithmetic<Gf64>>::dot(a, b),
                "dot n={n} offset={offset}"
            );
            for scale in [0, 1, 1 << 63, u64::MAX, mix(n as u64)] {
                let mut actual = vec![u64::MAX; 48];
                let mut expected = actual.clone();
                <Vpclmul512 as Arithmetic<Gf64>>::scale_xor(
                    &mut actual[offset..offset + n],
                    a,
                    scale,
                );
                <Portable as Arithmetic<Gf64>>::scale_xor(
                    &mut expected[offset..offset + n],
                    a,
                    scale,
                );
                assert_eq!(actual, expected, "scale_xor n={n} offset={offset}");
            }
            let mut actual = vec![u64::MAX; 48];
            let mut expected = actual.clone();
            <Vpclmul512 as Arithmetic<Gf64>>::square_slice(&mut actual[offset..offset + n], a);
            <Portable as Arithmetic<Gf64>>::square_slice(&mut expected[offset..offset + n], a);
            assert_eq!(actual, expected, "square_slice n={n} offset={offset}");
            <Vpclmul512 as BulkKernels<Gf64>>::xor_assign(&mut actual[offset..offset + n], b);
            <Portable as BulkKernels<Gf64>>::xor_assign(&mut expected[offset..offset + n], b);
            assert_eq!(actual, expected, "xor n={n} offset={offset}");
            for degree in [0, 1, 2, 3, 4, 8, 18, 32] {
                <Vpclmul512 as BulkKernels<Gf64>>::horner_many(
                    &a[..degree.min(n)],
                    b,
                    &mut actual[offset..offset + n],
                );
                <Portable as BulkKernels<Gf64>>::horner_many(
                    &a[..degree.min(n)],
                    b,
                    &mut expected[offset..offset + n],
                );
                assert_eq!(actual, expected, "horner n={n} offset={offset}");
            }
        }
    }
}

#[test]
fn insert_schedules_and_tiles() {
    if !vector::available() {
        return;
    }
    let ids: Vec<_> = (1..=512).map(mix).collect();
    for capacity in (1..=100).chain([18, 32, 72, 89]) {
        for n in [0, 1, 2, 3, 4, 5, 7, 8, 9, 15, 16, 17, 31, 32, 33, 64, 512] {
            let mut actual = vec![0; capacity];
            let mut expected = actual.clone();
            <Vpclmul512 as BulkKernels<Gf64>>::insert_nonzero(&mut actual, &ids[..n]);
            <Portable as BulkKernels<Gf64>>::insert_nonzero(&mut expected, &ids[..n]);
            assert_eq!(actual, expected, "insert c={capacity} n={n}");
            <Vpclmul512 as BulkKernels<Gf64>>::insert_nonzero(&mut actual, &ids[..n]);
            assert_eq!(
                actual,
                vec![0; capacity],
                "insert parity c={capacity} n={n}"
            );
        }
    }
}
