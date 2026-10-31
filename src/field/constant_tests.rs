#![forbid(unsafe_code)]

use {
    super::{Gf64, maps, reference},
    std::cell::Cell,
};

#[test]
fn quadratic_chunks_regenerate_from_scalar_field() {
    let mut matrix = [0_u64; 64];
    let mut rhs = [0_u64; 64];
    for column in 1..64 {
        let input = 1_u64 << column;
        let image = reference::mul::<Gf64>(input, input) ^ input;
        for (row, coefficients) in matrix.iter_mut().enumerate() {
            *coefficients |= ((image >> row) & 1) << column;
        }
    }
    for (row, value) in rhs.iter_mut().enumerate() {
        *value = 1_u64 << row;
    }
    let mut rows = [0_u64; 64];
    let mut rank = 0;
    for column in 1..64 {
        let mask = 1_u64 << column;
        let pivot = (rank..64).find(|&row| matrix[row] & mask != 0).unwrap();
        matrix.swap(rank, pivot);
        rhs.swap(rank, pivot);
        let pivot_matrix = matrix[rank];
        let pivot_rhs = rhs[rank];
        for row in 0..64 {
            if row != rank && matrix[row] & mask != 0 {
                matrix[row] ^= pivot_matrix;
                rhs[row] ^= pivot_rhs;
            }
        }
        rank += 1;
    }
    assert_eq!(rank, 63, "Q has kernel {{0,1}}");
    rows[1..].copy_from_slice(&rhs[..rank]);
    for (chunk, table) in super::quadratic_chunks::GF64_QUADRATIC_CHUNKS
        .iter()
        .enumerate()
    {
        for (nibble, &actual) in table.iter().enumerate() {
            let input = u64::try_from(nibble).unwrap() << (4 * chunk);
            let expected = rows.iter().enumerate().fold(0, |value, (bit, row)| {
                value | (u64::from((row & input).count_ones() & 1) << bit)
            });
            assert_eq!(actual, expected, "quadratic chunk {chunk}, nibble {nibble}");
        }
    }
}

#[test]
fn inverse_keeps_itoh_tsujii_schedule() {
    for input in [0, 1, 2, u64::MAX, 1 << 63] {
        let products = Cell::new(0);
        let squares = Cell::new(0);
        let result = maps::inverse_using::<Gf64>(
            input,
            |left, right| {
                products.set(products.get() + 1);
                reference::mul::<Gf64>(left, right)
            },
            |value| {
                squares.set(squares.get() + 1);
                reference::mul::<Gf64>(value, value)
            },
        );
        let expected = if input <= 1 { (0, 0) } else { (10, 63) };
        assert_eq!(
            (products.get(), squares.get()),
            expected,
            "fixed inversion schedule"
        );
        if input == 0 {
            assert_eq!(result, None);
        } else {
            assert_eq!(reference::mul::<Gf64>(input, result.unwrap()), 1);
        }
    }
}

#[test]
fn trace_matches_canonical_basis() {
    for bit in 0..64 {
        let input = 1_u64 << bit;
        let mut conjugate = input;
        let mut trace = input;
        for _ in 1..64 {
            conjugate = reference::mul::<Gf64>(conjugate, conjugate);
            trace ^= conjugate;
        }
        assert!(trace <= 1, "canonical absolute trace is binary");
        assert_eq!(
            u64::from(maps::trace::<Gf64>(input)),
            trace,
            "trace on basis coordinate {bit}"
        );
    }
}
