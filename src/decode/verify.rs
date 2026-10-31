//! Exact odd-syndrome verification rebuilt only from the returned roots.
#![forbid(unsafe_code)]

use crate::{backend::contract::BulkKernels, field::BinaryField};

/// Instruction counts for the existing eight-lane native kernels. These are a
/// dispatch model, never logical work charges or an estimate of elapsed time.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ProductCounts {
    pub(crate) raw: u64,
    pub(crate) including_reduction: u64,
}

/// The wire admits at most u16::MAX words per row. The model is evaluated in u64
/// after checking that bound, independently of the selected arithmetic backend.
pub(crate) fn product_counts(
    degree: usize,
    capacity: usize,
) -> Option<(ProductCounts, ProductCounts)> {
    if degree > capacity || capacity > usize::from(u16::MAX) {
        return None;
    }
    let d = degree as u64;
    let c = capacity as u64;
    let complete_tiles = d / 32;
    let remainder = d % 32;
    let tail_vectors = match remainder {
        0 => 0,
        1..=8 => 1,
        9..=16 => 2,
        _ => 4,
    };
    let vectors = 4 * complete_tiles + tail_vectors;
    // Complete 32-ID tiles and 17..32 tails use shift reduction. Smaller tails
    // use two CLMUL reductions per raw product, four per eight-lane multiply.
    let reduced_vectors = if remainder <= 16 { tail_vectors } else { 0 };
    let current = ProductCounts {
        raw: 2 * vectors * c,
        including_reduction: (2 * vectors + 4 * reduced_vectors) * c,
    };
    let blocks = d / 8;
    let locator_vectors = 4 * blocks * (blocks + 1) + (blocks + 1) * (d % 8);
    let continuation_blocks = (c - d).div_ceil(8);
    let rebuilt = ProductCounts {
        raw: 2 * (locator_vectors + vectors * d + d * continuation_blocks) + d,
        including_reduction: 6 * locator_vectors
            + (2 * vectors + 4 * reduced_vectors) * d
            + 3 * d
            + (2 * d + 4) * continuation_blocks,
    };
    Some((current, rebuilt))
}

/// Preserve the established tiny paths. For larger candidates use rebuilt LFSR
/// only when neither carryless-product count increases and at least one falls.
/// The same dimensions select the same method on every backend.
pub(crate) fn use_rebuilt_lfsr(degree: usize, capacity: usize) -> bool {
    if degree <= 2 {
        return false;
    }
    let Some((current, rebuilt)) = product_counts(degree, capacity) else {
        return false;
    };
    rebuilt.raw <= current.raw
        && rebuilt.including_reduction <= current.including_reduction
        && rebuilt != current
}

/// Rebuild L(z)=product(1+root*z), directly encode and compare the first d odd
/// words, then check every remaining word against L's squared-coefficient
/// recurrence. The BM locator is deliberately neither read nor trusted.
///
/// The caller charges before entering, and supplies d+1 coefficient words and
/// min(d,c) expected-prefix words. No allocation or retained cross-row state.
pub(crate) fn rebuilt_lfsr<F: BinaryField, K: BulkKernels<F>>(
    roots: &[u64],
    odd: &[u64],
    coefficients: &mut [u64],
    expected: &mut [u64],
) -> bool {
    let degree = roots.len();
    let prefix = degree.min(odd.len());
    let coefficients = &mut coefficients[..=degree];
    coefficients.fill(0);
    coefficients[0] = 1;
    for (index, &root) in roots.iter().enumerate() {
        K::multiply_linear(&mut coefficients[..index + 2], root);
    }
    let expected = &mut expected[..prefix];
    expected.fill(0);
    K::insert_nonzero(expected, roots);
    if expected != &odd[..prefix] {
        return false;
    }
    for coefficient in &mut coefficients[1..] {
        *coefficient = K::square(*coefficient);
    }
    K::odd_recurrence_matches(odd, coefficients)
}

#[cfg(test)]
mod tests;
