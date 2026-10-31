//! Speculative field-root derivation. A result still needs complete row verification.
#![forbid(unsafe_code)]

use crate::{backend::contract::BulkKernels, field::BinaryField};

pub(super) struct Pair {
    pub(super) roots: [u64; 2],
    #[cfg(test)]
    pub(crate) algebra: (u64, u64, u64),
}

#[cfg(test)]
#[derive(Clone, Copy, Debug, Default)]
pub(crate) enum Fault {
    #[default]
    None,
    BadMap,
    EqualRoots,
    ZeroRoot,
}

pub(super) fn two<F: BinaryField, K: BulkKernels<F>>(
    s: u64,
    syndrome3: u64,
    #[cfg(test)] fault: Fault,
) -> Option<Pair> {
    let inverse = K::inverse(s).expect("eligible nonzero S1");
    let square = K::square(s);
    let cube = K::mul(square, s);
    let product = K::mul(syndrome3 ^ cube, inverse);
    if product == 0 {
        return None;
    }
    let target = K::mul(product, K::square(inverse));
    let solution = K::solve_quadratic(target)?;
    #[cfg(test)]
    let solution = if matches!(fault, Fault::BadMap) {
        solution ^ 2
    } else {
        solution
    };
    if solution & !F::MASK != 0 || K::square(solution) ^ solution != target {
        return None;
    }
    let first = K::mul(s, solution);
    let roots = [first, first ^ s];
    #[cfg(test)]
    let roots = match fault {
        Fault::EqualRoots => [first, first],
        Fault::ZeroRoot => [0, roots[1]],
        Fault::None | Fault::BadMap => roots,
    };
    if roots[0] == roots[1] || roots.iter().any(|&root| root == 0 || root & !F::MASK != 0) {
        return None;
    }
    Some(Pair {
        roots,
        #[cfg(test)]
        algebra: (product, target, solution),
    })
}
