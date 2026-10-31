//! Algebra controls generated independently with integer GF64 arithmetic by a separate script (not included).
use {
    super::*,
    crate::{
        backend::portable::Portable,
        field::{Gf64, reference},
    },
};
fn product(roots: &[u64]) -> Vec<u64> {
    let mut p = vec![1];
    for &r in roots {
        let mut next = vec![0; p.len() + 1];
        for (i, &v) in p.iter().enumerate() {
            next[i] ^= reference::mul::<Gf64>(v, r);
            next[i + 1] ^= v;
        }
        p = next;
    }
    p
}
fn power(mut x: u64, mut exponent: u64) -> u64 {
    let mut out = 1;
    while exponent != 0 {
        if exponent & 1 != 0 {
            out = reference::mul::<Gf64>(out, x);
        }
        x = reference::mul::<Gf64>(x, x);
        exponent >>= 1;
    }
    out
}
#[test]
fn independent_algebra_and_solver_controls() {
    assert_eq!(OMEGA, 0x19c9_369f_278a_dc02);
    assert_eq!(OMEGA & 1, 0);
    assert_eq!(power(OMEGA, 2), OMEGA ^ 1);
    assert_eq!(power(OMEGA, 3), 1);
    assert_ne!(OMEGA, 1);
    for x in [1, 2, 3, 0x1234_5678_9abc_def0, u64::MAX] {
        let cube = power(x, 3);
        assert_eq!(
            cube_root::<Gf64, Portable>(cube),
            Some(power(cube, 0x1c71_c71c_71c7_1c72))
        );
    }
    for (degree, odd, cleared, denominator, locator) in [
        (
            3,
            vec![0, 6, 0x12, 0x7e, 0x102, 0x70e],
            vec![0x14, 0x12, 0, 6],
            6,
            vec![6, 7, 0, 1],
        ),
        (
            4,
            vec![0, 0x22, 0x356, 0x2d5a, 0x30506, 0x2b636a, 0x3705076],
            vec![0xe0e0, 0x8888, 0x6c6c, 0, 0x404],
            0x404,
            vec![0x38, 0x22, 0x1b, 0, 1],
        ),
    ] {
        let mut nums = [0; 6];
        let mut actual = [0; 5];
        assert!(guard::<Gf64, Portable>(&odd, degree, &mut nums));
        assert_eq!(&nums[..=degree], cleared);
        assert_eq!(nums[5], denominator);
        normalize::<Gf64, Portable>(&nums, odd[0], degree, &mut actual);
        assert_eq!(&actual[..=degree], locator);
    }
    for roots in [
        vec![1, 2, 3],
        vec![1, 2, 4],
        vec![1, OMEGA, OMEGA ^ 1],
        vec![1, 2, 4, 7],
        vec![1, 2, 3, 4],
        vec![1, 2, 4, 0xdb6d_b6db_6db6_db66],
    ] {
        let p = product(&roots);
        let mut output = [0; 4];
        let count = solve::<Gf64, Portable>(&p, &mut output).expect("split positive");
        assert_eq!(count, roots.len());
        assert!(certificate::<Gf64, Portable>(
            &p,
            &output[..count],
            &mut [0; 5]
        ));
        output[..count].sort_unstable();
        let mut roots = roots;
        roots.sort_unstable();
        assert_eq!(&output[..count], roots);
    }
    for p in [
        vec![2, 0, 0, 1],
        vec![0, 1, 0, 1],
        vec![0, 0, 0, 1],
        vec![2, 1, 2, 1],
        vec![1, 0x20_0000, 0, 1],
        vec![1, 0, 0, 0, 1],
        vec![1, 1, 0, 1, 1],
        vec![1, 2, 0, 0, 1],
        vec![0x8000_0000_0000_0036, 6, 7, 0, 1],
        vec![0xac00_0000_0000_0000, 6, 7, 0, 1],
    ] {
        assert!(
            solve::<Gf64, Portable>(&p, &mut [0; 4]).is_none(),
            "solver must miss before certification: {p:x?}"
        );
    }
    for p in [vec![0, 2, 3, 1], vec![0, 6, 7, 0, 1]] {
        let mut out = [0; 4];
        let count = solve::<Gf64, Portable>(&p, &mut out).unwrap();
        assert!(
            !certificate::<Gf64, Portable>(&p, &out[..count], &mut [0; 5]),
            "field zero must fail certification"
        );
    }
    let p = product(&[1, 2, 3]);
    for roots in [vec![1, 2, 4], vec![1, 2, 2], vec![0, 1, 2], vec![1, 2]] {
        assert!(
            !certificate::<Gf64, Portable>(&p, &roots, &mut [0; 5]),
            "complete product certificate must reject {roots:?}"
        );
    }
}
