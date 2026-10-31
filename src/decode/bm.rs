//! Binary power sums force every odd-index discrepancy to zero.
#![forbid(unsafe_code)]

use {
    super::work::{Charge, WorkScheduleV1},
    crate::{
        backend::contract::BulkKernels,
        field::BinaryField,
        types::{DecodeError, DecodeFailure, WorkMeter},
    },
};

/// The first buffer becomes the monic reciprocal; all writes stay within budget+1.
pub(super) fn locator<F: BinaryField, K: BulkKernels<F>>(
    syndromes: &[u64],
    capacity: usize,
    budget: usize,
    buffers: &mut [u64],
    meter: &mut WorkMeter,
) -> Result<Result<usize, DecodeFailure>, DecodeError> {
    let cost = WorkScheduleV1::cost(Charge::BmStep { budget })?;
    meter.charge(cost)?;
    let width = capacity + 1;
    let (connection, rest) = buffers.split_at_mut(width);
    let (previous, rest) = rest.split_at_mut(width);
    let (saved, _) = rest.split_at_mut(width);
    connection[..=budget].fill(0);
    previous[..=budget].fill(0);
    connection[0] = 1;
    previous[0] = 1;
    let (mut degree, mut previous_len, mut shift, mut previous_delta) = (0, 1, 1, 1);
    for n in 0..2 * capacity {
        if n != 0 {
            meter.charge(cost)?;
        }
        // S(2k)=S(k)^2 makes these discrepancies zero, even for arbitrary odd rows.
        let delta = if n.is_multiple_of(2) {
            // Homogeneous C no longer has a unit constant. Accumulate the full
            // scalar discrepancy directly, avoiding the old reversal bookkeeping.
            let mut product = crate::types::RawProduct { lo: 0, hi: 0 };
            for (&coefficient, &syndrome) in connection[..=degree]
                .iter()
                .zip(syndromes[n + 1 - degree..=n + 1].iter().rev())
            {
                let term = K::raw_mul(coefficient, syndrome);
                product.lo ^= term.lo;
                product.hi ^= term.hi;
            }
            K::reduce(product)
        } else {
            0
        };
        if delta == 0 {
            shift += 1;
            continue;
        }
        let grows = 2 * degree <= n;
        let next_degree = if grows { n + 1 - degree } else { degree };
        if next_degree > budget {
            return Ok(Err(DecodeFailure::DegreeExceedsBudget));
        }
        let len = degree + 1;
        if grows {
            saved[..len].copy_from_slice(&connection[..len]);
        }
        // C and the saved B may be scaled by different nonzero factors.
        // b*C + delta(C)*X^shift*B preserves the classical connection up to
        // scale, including every zero discrepancy and degree-growth decision.
        for coefficient in &mut connection[..len] {
            *coefficient = K::mul(previous_delta, *coefficient);
        }
        connection[len..=next_degree].fill(0);
        for (coefficient, &old) in connection[shift..shift + previous_len]
            .iter_mut()
            .zip(&previous[..previous_len])
        {
            *coefficient ^= K::mul(delta, old);
        }
        if grows {
            previous[..len].copy_from_slice(&saved[..len]);
            previous_len = len;
            degree = next_degree;
            previous_delta = delta;
            shift = 1;
        } else {
            shift += 1;
        }
    }
    if connection[degree] == 0 || connection[0] == 0 {
        return Ok(Err(DecodeFailure::InvalidLocator));
    }
    let inverse = K::inverse(connection[0]).expect("nonzero connection constant");
    for coefficient in &mut connection[..=degree] {
        *coefficient = K::mul(*coefficient, inverse);
    }
    connection[..=degree].reverse();
    Ok(Ok(degree))
}
