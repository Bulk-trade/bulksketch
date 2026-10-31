//! Versioned logical charges: V2 adds tiny probes; proposed V3 adds affine roots
//! and independently rebuilt odd-LFSR verification. V1/V2 charges stay frozen.
//! These are dimension charges, not CPU estimates.
//!
//! Charge before the named operation, even if a scalar/vector shortcut would avoid work.
//! Preflight shape/plan/zero-budget scanning costs zero. A row preclassified by zero
//! underflow has no row charges. An equal row pays Compare only. Every admitted request
//! pays Admission and Normalize once, including requests whose rows all fail or are equal.
//! Compare also writes the complete odd difference into its separate immutable row
//! input segment. Reconstruction/BM/verification never overwrite that input.
//! No cross-request algebra cache may change a charge. All row stages use the original
//! nonzero budget for BM, original locator degree for candidate evaluation/deflation,
//! current factor degree for root operations, and beta for verification/canonicalization.
#![forbid(unsafe_code)]

use crate::types::{DecodeError, WorkUnits};

/// Logical field-word envelopes, including V2 probes and proposed V3 kernels.
/// Padding is never a dimension.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Charge {
    Admission {
        rows: usize,
    },
    Normalize {
        inputs: usize,
    },
    Compare {
        capacity: usize,
    },
    DirectOne,
    DirectTwo,
    GuardThree,
    NewtonThree,
    GuardFour,
    NewtonFour,
    LeafThree,
    LeafFour,
    FactorVerification {
        degree: usize,
    },
    Reconstruct {
        capacity: usize,
    },
    BmStep {
        budget: usize,
    },
    Candidates {
        degree: usize,
        inputs: usize,
    },
    Deflate {
        degree: usize,
    },
    AffinePreparation {
        degree: usize,
    },
    AffineEnumeration {
        degree: usize,
        rank: usize,
    },
    AffineSplit {
        degree: usize,
        rank: usize,
    },
    VerifyLfsr {
        capacity: usize,
        output_budget: usize,
        degree: usize,
    },
    Table {
        degree: usize,
    },
    Trace {
        degree: usize,
    },
    SplitCheck {
        degree: usize,
    },
    Gcd {
        degree: usize,
    },
    Divide {
        degree: usize,
    },
    SplitAssembly {
        degree: usize,
    },
    Leaf {
        degree: usize,
    },
    Verify {
        capacity: usize,
        output_budget: usize,
    },
    Canonicalize {
        ids: usize,
    },
}

pub(crate) struct WorkScheduleV1;

impl WorkScheduleV1 {
    /// The constants reserve a fixed inversion envelope of 128 field operations.
    /// Degree-dependent polynomial charges include normalization/copies. A driver
    /// charges each macro once; kernels underneath do not recursively charge it again.
    #[inline(always)]
    pub(crate) fn cost(charge: Charge) -> Result<WorkUnits, DecodeError> {
        let cost = match charge {
            Charge::Admission { rows } => add(1, number(rows)?)?,
            Charge::Normalize { inputs } => mul(number(inputs)?, add(log2_ceil(inputs), 3)?)?,
            Charge::Compare { capacity } => add(number(capacity)?, 1)?,
            Charge::DirectOne => 1,
            Charge::DirectTwo => 168,
            Charge::GuardThree => 48,
            Charge::NewtonThree => 144,
            Charge::GuardFour => 80,
            Charge::NewtonFour => 160,
            Charge::LeafThree => 640,
            Charge::LeafFour => 2048,
            Charge::FactorVerification { degree } => {
                add(add(mul(2, square(degree)?)?, mul(4, number(degree)?)?)?, 1)?
            }
            Charge::Reconstruct { capacity } => mul(3, number(capacity)?)?,
            Charge::BmStep { budget } => add(mul(6, add(number(budget)?, 1)?)?, 128)?,
            Charge::Candidates { degree, inputs } => {
                mul(mul(2, number(inputs)?)?, add(number(degree)?, 1)?)?
            }
            Charge::Deflate { degree } => mul(mul(2, number(degree)?)?, add(number(degree)?, 1)?)?,
            Charge::AffinePreparation { degree } => {
                let d = number(degree)?;
                let d2 = mul(d, d)?;
                add(
                    add(mul(5, mul(d2, d)?)?, mul(16, d2)?)?,
                    add(mul(327, d)?, 16900)?,
                )?
            }
            Charge::AffineEnumeration { degree, rank } => {
                let points = 1_u64
                    .checked_shl(u32::try_from(rank).map_err(|_| DecodeError::WorkLimitExceeded)?)
                    .ok_or(DecodeError::WorkLimitExceeded)?;
                add(
                    mul(mul(2, points)?, add(number(degree)?, 2)?)?,
                    add(number(degree)?, 1)?,
                )?
            }
            Charge::AffineSplit { degree, rank } => {
                let d = number(degree)?;
                add(
                    mul(
                        number(rank)?,
                        add(square_mod(degree)?, add(mul(3, d)?, 3)?)?,
                    )?,
                    add(mul(3, d)?, 1)?,
                )?
            }

            Charge::VerifyLfsr {
                capacity,
                output_budget,
                degree,
            } => add(
                mul(add(mul(3, number(degree)?)?, 4)?, number(capacity)?)?,
                add(number(degree)?, add(number(output_budget)?, 3)?)?,
            )?,
            Charge::Table { degree } => add(mul(8, square(degree)?)?, mul(2, number(degree)?)?)?,
            Charge::Trace { degree } => mul(63, add(square_mod(degree)?, 2)?)?,
            Charge::SplitCheck { degree } => add(square_mod(degree)?, add(number(degree)?, 1)?)?,
            Charge::Gcd { degree } => {
                let n = add(number(degree)?, 1)?;
                add(mul(8, mul(n, n)?)?, mul(128, n)?)?
            }
            Charge::Divide { degree } => {
                let n = add(number(degree)?, 1)?;
                add(mul(4, mul(n, n)?)?, 128)?
            }
            Charge::SplitAssembly { degree } => mul(4, add(number(degree)?, 1)?)?,
            Charge::Leaf { degree } => match degree {
                0 => 0,
                1 => 1,
                2 => 160,
                _ => panic!("leaf degree must be at most two"),
            },
            Charge::Verify {
                capacity,
                output_budget,
            } => {
                let beta = number(output_budget)?;
                add(
                    mul(add(mul(2, beta)?, 3)?, number(capacity)?)?,
                    add(beta, 1)?,
                )?
            }
            Charge::Canonicalize { ids } => mul(number(ids)?, add(log2_ceil(ids), 1)?)?,
        };
        Ok(WorkUnits(cost))
    }

    /// Worst proper split tree. For increasing convex node costs, an unbalanced
    /// chain maximizes their sum: at most one node of each size 3..=r is sufficient
    /// as a bound. At each node all 64 trace directions and split checks are charged.
    /// 160*r additionally bounds every possible degree-one/two leaf partition.
    #[inline(always)]
    pub(crate) fn roots_bound(budget: usize) -> Result<WorkUnits, DecodeError> {
        let r = number(budget)?;
        let leaves = mul(160, r)?;
        if budget < 3 {
            return Ok(WorkUnits(leaves));
        }
        // Expanding one node's exact table gives 12812*d^2 + 17486*d + 16968.
        // Closed sums keep request admission O(B), independent of algebraic degree.
        let next = add(r, 1)?;
        let squares = mul(mul(r, next)?, add(mul(2, r)?, 1)?)? / 6;
        let linear = mul(r, next)? / 2;
        let squares = squares
            .checked_sub(5)
            .ok_or(DecodeError::WorkLimitExceeded)?;
        let linear = linear
            .checked_sub(3)
            .ok_or(DecodeError::WorkLimitExceeded)?;
        let nodes = r.checked_sub(2).ok_or(DecodeError::WorkLimitExceeded)?;
        let total = add(
            add(mul(12812, squares)?, mul(17486, linear)?)?,
            mul(16968, nodes)?,
        )?;
        Ok(WorkUnits(add(leaves, total)?))
    }

    #[inline(always)]
    pub(crate) fn row_bound(
        capacity: usize,
        budget: usize,
        beta: usize,
        candidates: usize,
    ) -> Result<WorkUnits, DecodeError> {
        let fixed = sum_costs(&[
            Charge::Compare { capacity },
            Charge::Reconstruct { capacity },
            Charge::Candidates {
                degree: budget,
                inputs: candidates,
            },
            Charge::Deflate { degree: budget },
            Charge::Verify {
                capacity,
                output_budget: beta,
            },
            Charge::Canonicalize { ids: beta },
        ])?;
        let bm = mul(
            mul(2, number(capacity)?)?,
            Self::cost(Charge::BmStep { budget })?.0,
        )?;
        Ok(WorkUnits(add(
            add(fixed, bm)?,
            Self::roots_bound(budget)?.0,
        )?))
    }
}

pub(crate) struct WorkScheduleV2;

impl WorkScheduleV2 {
    #[inline(always)]
    pub(crate) fn row_bound(
        capacity: usize,
        budget: usize,
        beta: usize,
        candidates: usize,
    ) -> Result<WorkUnits, DecodeError> {
        let mut bound = WorkScheduleV1::row_bound(capacity, budget, beta, candidates)?.0;
        let verify = WorkScheduleV1::cost(Charge::Verify {
            capacity,
            output_budget: beta,
        })?
        .0;
        if budget >= 1 {
            bound = add(
                bound,
                add(WorkScheduleV1::cost(Charge::DirectOne)?.0, verify)?,
            )?;
        }
        if capacity >= 2 && budget >= 2 {
            bound = add(
                bound,
                add(WorkScheduleV1::cost(Charge::DirectTwo)?.0, verify)?,
            )?;
        }
        Ok(WorkUnits(bound))
    }
}

#[inline(always)]
fn square_mod(degree: usize) -> Result<u64, DecodeError> {
    add(mul(3, square(degree)?)?, mul(2, number(degree)?)?)
}
#[inline(always)]
fn square(n: usize) -> Result<u64, DecodeError> {
    mul(number(n)?, number(n)?)
}
#[inline(always)]
pub(crate) fn number(n: usize) -> Result<u64, DecodeError> {
    u64::try_from(n).map_err(|_| DecodeError::WorkLimitExceeded)
}
#[inline(always)]
pub(crate) fn add(a: u64, b: u64) -> Result<u64, DecodeError> {
    a.checked_add(b).ok_or(DecodeError::WorkLimitExceeded)
}
#[inline(always)]
fn mul(a: u64, b: u64) -> Result<u64, DecodeError> {
    a.checked_mul(b).ok_or(DecodeError::WorkLimitExceeded)
}
#[inline(always)]
fn sum_costs(charges: &[Charge]) -> Result<u64, DecodeError> {
    charges
        .iter()
        .try_fold(0, |n, &c| add(n, WorkScheduleV1::cost(c)?.0))
}
#[inline(always)]
fn log2_ceil(n: usize) -> u64 {
    if n <= 1 {
        0
    } else {
        u64::from(usize::BITS - (n - 1).leading_zeros())
    }
}

/// Proposed V3 reserves extra affine stages and the larger general verifier.
pub(crate) struct WorkScheduleV3;
impl WorkScheduleV3 {
    #[inline(always)]
    pub(crate) fn row_bound(
        capacity: usize,
        budget: usize,
        beta: usize,
        candidates: usize,
    ) -> Result<WorkUnits, DecodeError> {
        let mut bound = WorkScheduleV2::row_bound(capacity, budget, beta, candidates)?.0;
        let original = WorkScheduleV1::cost(Charge::Verify {
            capacity,
            output_budget: beta,
        })?
        .0;
        let rebuilt = WorkScheduleV1::cost(Charge::VerifyLfsr {
            capacity,
            output_budget: beta,
            degree: budget,
        })?
        .0;
        bound = add(bound, rebuilt.max(original) - original)?;
        // The maximum is const-derived from the operation predictor, never a
        // tuned admission parameter. Each new charge is monotone in d/rank.
        let d = budget.min(super::affine::MAX_PREFERRED_DEGREE);
        if d >= 3 {
            let setup = WorkScheduleV1::cost(Charge::AffinePreparation { degree: d })?.0;
            let enumeration = WorkScheduleV1::cost(Charge::AffineEnumeration {
                degree: d,
                rank: d - 1,
            })?
            .0;
            let split = WorkScheduleV1::cost(Charge::AffineSplit {
                degree: d,
                rank: d - 1,
            })?
            .0;
            let attempts = mul(number(d)?, number(d - 2)?)?;
            bound = add(bound, add(setup, enumeration.max(mul(attempts, split)?))?)?;
        }
        // Retain all integrated affine/LFSR fallback work, then add the degree-3/4 guards and leaves.
        if capacity >= 3 && budget >= 3 {
            bound = add(bound, add(863, original)?)?;
        }
        if capacity >= 4 && budget >= 4 {
            bound = add(bound, add(2337, original)?)?;
        }
        bound = add(
            bound,
            add(
                mul(671, number(budget / 3)?)?,
                mul(2097, number(budget / 4)?)?,
            )?,
        )?;
        Ok(WorkUnits(bound))
    }
}
