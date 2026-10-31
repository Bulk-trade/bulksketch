#![forbid(unsafe_code)]

use {
    super::{
        contract::{Arithmetic, BulkKernels},
        portable::Portable,
        x86_pclmul::{Pclmul, reduce_cl_for_test},
    },
    crate::{
        field::{Gf64, reference},
        types::RawProduct,
    },
};

type Hardware = Pclmul;

fn mix(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

#[test]
fn pclmul_products_and_reductions() {
    if !std::is_x86_feature_detected!("pclmulqdq") {
        return;
    }
    let mut operands = vec![0, 1, u64::MAX, 1 << 63, 0xaaaa_aaaa_aaaa_aaaa];
    operands.extend((0..64).map(|bit| 1_u64 << bit));
    operands.extend((0..64).map(mix));
    for &left in &operands {
        for &right in &operands {
            let product = <Hardware as Arithmetic<Gf64>>::raw_mul(left, right);
            assert_eq!(
                product,
                reference::raw_mul::<Gf64>(left, right),
                "raw product {left:x} {right:x}"
            );
            let expected = reference::reduce::<Gf64>(product);
            assert_eq!(<Hardware as Arithmetic<Gf64>>::reduce(product), expected);
            assert_eq!(
                reduce_cl_for_test(product),
                expected,
                "CL reduction {left:x} {right:x}"
            );
            assert_eq!(<Hardware as Arithmetic<Gf64>>::mul(left, right), expected);
        }
    }
    for index in 0..1024 {
        let product = RawProduct {
            lo: mix(index),
            hi: mix(index ^ 0x8000),
        };
        let expected = reference::reduce::<Gf64>(product);
        assert_eq!(
            <Hardware as Arithmetic<Gf64>>::reduce(product),
            expected,
            "full-width reduction"
        );
        assert_eq!(
            reduce_cl_for_test(product),
            expected,
            "full-width CL reduction"
        );
    }
    assert_eq!(
        reduce_cl_for_test(RawProduct {
            lo: u64::MAX,
            hi: u64::MAX
        }),
        reference::reduce::<Gf64>(RawProduct {
            lo: u64::MAX,
            hi: u64::MAX
        })
    );
}

#[test]
fn pclmul_maps_and_inverse() {
    if !std::is_x86_feature_detected!("pclmulqdq") {
        return;
    }
    let mut inputs = vec![0, 1, u64::MAX];
    inputs.extend((0..64).map(|bit| 1_u64 << bit));
    inputs.extend((0..32).map(mix));
    for input in inputs {
        assert_eq!(
            <Hardware as Arithmetic<Gf64>>::square(input),
            reference::mul::<Gf64>(input, input)
        );
        let mut power = input;
        let mut trace = input;
        for exponent in 1..=64 {
            power = reference::mul::<Gf64>(power, power);
            assert_eq!(
                <Hardware as Arithmetic<Gf64>>::frobenius(input, exponent),
                power,
                "Frobenius {exponent}"
            );
            if exponent < 64 {
                trace ^= power;
            }
        }
        assert_eq!(
            u64::from(<Hardware as Arithmetic<Gf64>>::trace(input)),
            trace
        );
        assert_eq!(
            <Hardware as Arithmetic<Gf64>>::solve_quadratic(input),
            <Portable as Arithmetic<Gf64>>::solve_quadratic(input)
        );
        let inverse = <Hardware as Arithmetic<Gf64>>::inverse(input);
        assert_eq!(inverse, <Portable as Arithmetic<Gf64>>::inverse(input));
        if input == 0 {
            assert_eq!(inverse, None);
        } else {
            assert_eq!(
                reference::mul::<Gf64>(input, inverse.unwrap()),
                1,
                "inverse {input:x}"
            );
        }
    }
}

#[test]
fn pclmul_bulk_kernels() {
    if !std::is_x86_feature_detected!("pclmulqdq") {
        return;
    }
    for length in 0..=96 {
        for offset in 0..8 {
            let left: Vec<_> = (0..length).map(|i| mix(i as u64)).collect();
            let right: Vec<_> = (0..length).map(|i| mix(i as u64 + 1024)).collect();
            assert_eq!(
                <Hardware as Arithmetic<Gf64>>::dot(&left, &right),
                <Portable as Arithmetic<Gf64>>::dot(&left, &right)
            );
            for scale in [0, 1, u64::MAX, mix(length as u64)] {
                let mut hardware = vec![0x1234_5678_9abc_def0; length + offset + 8];
                let mut portable = hardware.clone();
                <Hardware as Arithmetic<Gf64>>::scale_xor(
                    &mut hardware[offset..offset + length],
                    &left,
                    scale,
                );
                <Portable as Arithmetic<Gf64>>::scale_xor(
                    &mut portable[offset..offset + length],
                    &left,
                    scale,
                );
                assert_eq!(
                    hardware, portable,
                    "scale {scale:x}, length {length}, offset {offset}"
                );
            }
            let mut hardware = vec![u64::MAX; length + offset + 8];
            let mut portable = hardware.clone();
            <Hardware as Arithmetic<Gf64>>::square_slice(
                &mut hardware[offset..offset + length],
                &left,
            );
            <Portable as Arithmetic<Gf64>>::square_slice(
                &mut portable[offset..offset + length],
                &left,
            );
            assert_eq!(
                hardware, portable,
                "squares length {length}, offset {offset}"
            );
        }
    }
    for capacity in [0, 1, 18, 32, 72, 89] {
        for count in 0..=17 {
            let ids: Vec<_> = (0..count).map(mix).collect();
            let mut hardware = vec![0; capacity];
            let mut portable = hardware.clone();
            <Hardware as BulkKernels<Gf64>>::insert_nonzero(&mut hardware, &ids);
            <Portable as BulkKernels<Gf64>>::insert_nonzero(&mut portable, &ids);
            assert_eq!(
                hardware, portable,
                "insert capacity {capacity}, count {count}"
            );
        }
    }
    for degree in 0..=12 {
        for count in 0..=25 {
            let coefficients: Vec<_> = (0..degree).map(mix).collect();
            let points: Vec<_> = (0..count).map(|i| mix(i + 128)).collect();
            let mut hardware = vec![0; usize::try_from(count).unwrap()];
            let mut portable = hardware.clone();
            <Hardware as BulkKernels<Gf64>>::horner_many(&coefficients, &points, &mut hardware);
            <Portable as BulkKernels<Gf64>>::horner_many(&coefficients, &points, &mut portable);
            assert_eq!(hardware, portable, "Horner degree {degree}, count {count}");
        }
    }
}
