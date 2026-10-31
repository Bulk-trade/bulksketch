//! Strategy obligations that field-valued equality cannot distinguish.
#![forbid(unsafe_code)]

use {
    super::{Dense, Polynomial, RawProduct},
    crate::{
        backend::{
            contract::{Arithmetic, BulkKernels},
            portable::Portable,
        },
        field::{BinaryField, Gf64},
    },
    std::cell::RefCell,
};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct Counts {
    raw: usize,
    reduce: usize,
    square: usize,
    inverse: usize,
    horner: usize,
}
thread_local! { static COUNTS: RefCell<Counts> = RefCell::new(Counts::default()); }
fn count(update: impl FnOnce(&mut Counts)) {
    COUNTS.with(|c| update(&mut c.borrow_mut()));
}
fn take() -> Counts {
    COUNTS.with(RefCell::take)
}

#[derive(Clone, Copy)]
struct Counted;
impl<F: BinaryField> Arithmetic<F> for Counted {
    fn mul(a: u64, b: u64) -> u64 {
        <Portable as Arithmetic<F>>::mul(a, b)
    }
    fn square(a: u64) -> u64 {
        count(|c| c.square += 1);
        <Portable as Arithmetic<F>>::square(a)
    }
    fn frobenius(a: u64, power: u32) -> u64 {
        <Portable as Arithmetic<F>>::frobenius(a, power)
    }
    fn inverse(a: u64) -> Option<u64> {
        count(|c| c.inverse += 1);
        <Portable as Arithmetic<F>>::inverse(a)
    }
    fn trace(a: u64) -> u8 {
        <Portable as Arithmetic<F>>::trace(a)
    }
    fn solve_quadratic(a: u64) -> Option<u64> {
        <Portable as Arithmetic<F>>::solve_quadratic(a)
    }
    fn raw_mul(a: u64, b: u64) -> RawProduct {
        count(|c| c.raw += 1);
        <Portable as Arithmetic<F>>::raw_mul(a, b)
    }
    fn reduce(p: RawProduct) -> u64 {
        count(|c| c.reduce += 1);
        <Portable as Arithmetic<F>>::reduce(p)
    }
    fn dot(a: &[u64], b: &[u64]) -> u64 {
        <Portable as Arithmetic<F>>::dot(a, b)
    }
    fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64) {
        <Portable as Arithmetic<F>>::scale_xor(dst, src, scale);
    }
    fn square_slice(dst: &mut [u64], src: &[u64]) {
        <Portable as Arithmetic<F>>::square_slice(dst, src);
    }
}
impl<F: BinaryField> BulkKernels<F> for Counted {
    fn insert_nonzero(odd: &mut [u64], ids: &[u64]) {
        <Portable as BulkKernels<F>>::insert_nonzero(odd, ids);
    }
    fn xor_assign(dst: &mut [u64], src: &[u64]) {
        <Portable as BulkKernels<F>>::xor_assign(dst, src);
    }
    fn horner_many(c: &[u64], p: &[u64], out: &mut [u64]) {
        count(|n| n.horner += 1);
        <Portable as BulkKernels<F>>::horner_many(c, p, out);
    }
}

#[test]
fn lazy_kernel_counts() {
    take();
    let (a, b) = ([u64::MAX; 4], [u64::MAX; 3]);
    let mut dst = [0; 8];
    let mut raw = [RawProduct::default(); 9];
    <Dense as Polynomial<Gf64, Counted>>::mul_into(&a, &b, &mut dst, &mut raw);
    assert_eq!(
        take(),
        Counts {
            raw: 12,
            reduce: 6,
            ..Counts::default()
        },
        "convolution reduces once per coefficient"
    );
    <Dense as Polynomial<Gf64, Counted>>::square_into(&a, &mut dst, &mut raw);
    assert_eq!(
        take(),
        Counts {
            square: 4,
            ..Counts::default()
        },
        "square uses characteristic two"
    );
    let mut q = [0; 5];
    let mut rem = [0; 5];
    <Dense as Polynomial<Gf64, Counted>>::div_rem_into(&a, &b, &mut q, &mut rem, &mut raw);
    assert_eq!(
        take(),
        Counts {
            raw: 0,
            reduce: 4,
            inverse: 1,
            ..Counts::default()
        },
        "division reduces each leading slot and final remainder; one inverse"
    );
    let modulus = [1, 0, 0, 1];
    let mut table = [0; 3];
    let mut work = [0; 16];
    <Dense as Polynomial<Gf64, Counted>>::prepare_square_table(&modulus, &mut table, &mut work);
    take();
    <Dense as Polynomial<Gf64, Counted>>::square_mod_into(
        &a[..3],
        &modulus,
        &table,
        &mut dst,
        &mut raw,
    );
    assert_eq!(
        take(),
        Counts {
            raw: 3,
            reduce: 3,
            square: 3,
            ..Counts::default()
        },
        "modular square reduces once per output"
    );
    <Dense as Polynomial<Gf64, Counted>>::eval_many_into(&a, &b, &mut dst[..3]);
    assert_eq!(
        take(),
        Counts {
            horner: 1,
            ..Counts::default()
        },
        "evaluation uses backend Horner"
    );
}
