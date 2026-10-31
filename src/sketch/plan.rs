//! Request bounds consume checked row dimensions, never lower-layer shape imports.
#![forbid(unsafe_code)]

use {
    super::scratch::ScratchLayout,
    crate::{
        decode::work::{Charge, WorkScheduleV1, WorkScheduleV2, WorkScheduleV3, add},
        types::{DecodeError, WorkUnits},
    },
};

/// An explicitly selected algorithm and logical charging policy, with no stage tuning.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecodePlan {
    pub(super) version: u8,
}

impl DecodePlan {
    /// Select direct tiny-difference probes with full verification and general fallback.
    #[must_use]
    pub const fn v2() -> Self {
        Self { version: 2 }
    }

    /// Select the proposed affine-root and rebuilt-LFSR logical schedule.
    #[must_use]
    pub const fn v3() -> Self {
        Self { version: 3 }
    }

    /// Retain the general-only schedule as a test oracle.
    #[cfg(test)]
    #[must_use]
    pub(crate) const fn v1() -> Self {
        Self { version: 1 }
    }

    /// Conservative work and complete scratch bounds after checked zero subtraction.
    /// `None` means zero subtraction underflowed for that row: metadata only.
    /// `beta` includes zero; every `Some(r)` must be beta or beta-1 and at most c.
    /// Candidate count is raw, before routing/deduplication.
    ///
    /// # Errors
    /// Invalid dimensions/budgets, work arithmetic overflow, or layout overflow.
    #[inline]
    pub fn complete_bound(
        &self,
        capacities: &[u16],
        row_budgets: &[Option<usize>],
        beta: usize,
        candidate_count: usize,
    ) -> Result<(WorkUnits, ScratchLayout), DecodeError> {
        self.validate(capacities, row_budgets, beta)?;
        let rows = capacities
            .iter()
            .zip(row_budgets)
            .map(|(&c, &r)| (usize::from(c), r));
        let work = self.work_bound(rows.clone(), beta, candidate_count)?;
        let layout = ScratchLayout::from_rows(rows, beta, candidate_count)?;
        Ok((work, layout))
    }

    pub(super) fn validate(
        self,
        capacities: &[u16],
        budgets: &[Option<usize>],
        beta: usize,
    ) -> Result<(), DecodeError> {
        if !self.is_supported()
            || capacities.is_empty()
            || capacities.len() != budgets.len()
            || capacities.iter().zip(budgets).any(|(&c, &r)| {
                c == 0
                    || beta > usize::from(c)
                    || r.is_some_and(|r| r > beta || beta - r > 1)
                    || (r.is_none() && beta != 0)
            })
        {
            return Err(DecodeError::InvalidPlan);
        }
        Ok(())
    }

    pub(super) fn is_supported(self) -> bool {
        self.version == 3 || self.version == 2 || (cfg!(test) && self.version == 1)
    }

    pub(super) fn is_v2(self) -> bool {
        self.version == 2
    }

    pub(super) fn is_v3(self) -> bool {
        self.version == 3
    }
    pub(super) fn has_probes(self) -> bool {
        self.version >= 2
    }

    pub(super) fn work_bound(
        self,
        rows: impl ExactSizeIterator<Item = (usize, Option<usize>)>,
        beta: usize,
        candidates: usize,
    ) -> Result<WorkUnits, DecodeError> {
        let mut total = WorkScheduleV1::cost(Charge::Admission { rows: rows.len() })?.0;
        total = add(
            total,
            WorkScheduleV1::cost(Charge::Normalize { inputs: candidates })?.0,
        )?;
        let mut previous = None;
        for (capacity, budget) in rows {
            if let Some(budget) = budget {
                let bound = match previous {
                    Some((c, r, bound)) if c == capacity && r == budget => bound,
                    _ => {
                        let bound = if self.is_v3() {
                            WorkScheduleV3::row_bound(capacity, budget, beta, candidates)?
                        } else if self.is_v2() {
                            WorkScheduleV2::row_bound(capacity, budget, beta, candidates)?
                        } else {
                            WorkScheduleV1::row_bound(capacity, budget, beta, candidates)?
                        };
                        previous = Some((capacity, budget, bound));
                        bound
                    }
                };
                total = add(total, bound.0)?;
            }
        }
        Ok(WorkUnits(total))
    }
}
