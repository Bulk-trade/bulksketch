//! Shared request admission and transactional publication for the decode job.
#![forbid(unsafe_code)]

use {
    super::{
        input::RequestInput,
        plan::DecodePlan,
        scratch::{DecodeScratch, ResultStorage, ScratchLayout},
        state::FrozenSketch,
        wire::SketchView,
    },
    crate::{
        decode::work::{Charge, WorkScheduleV1},
        field::BinaryField,
        types::{DecodeError, DecodeFailure, WorkMeter, WorkUnits},
    },
};

/// Request-wide resource caps; beta is also each row's total output budget, including zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecodeLimits {
    /// Must be at most every row capacity.
    pub max_output_per_bucket: usize,
    /// Raw hints, before routing, removal of zero or deduplication.
    pub max_candidate_inputs: usize,
    /// One meter for preprocessing and all rows.
    pub max_work: WorkUnits,
    /// Required typed arena bytes, including all outcomes and results.
    pub max_scratch_bytes: usize,
}

/// Explicit immutable reference and already parsed remote view. Hints never authorize output.
#[derive(Clone, Copy, Debug)]
pub struct DecodeRequest<'a, F: BinaryField> {
    /// Owned immutable local generation.
    pub local: &'a FrozenSketch<F>,
    /// Borrowed, fully admitted remote bytes.
    pub remote: SketchView<'a, F>,
    /// Original-ID hints, including possible repeats/zero.
    pub candidates: &'a [u64],
    /// Explicit versioned algorithm and charge schedule.
    pub plan: &'a DecodePlan,
    /// Request and row budget caps.
    pub limits: &'a DecodeLimits,
}

/// A completed row. Failure never denotes empty membership.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DecodeOutcome<'a> {
    /// The complete difference representation, including zero, was zero.
    Equal,
    /// Nonempty, strictly ascending original IDs, all fully verified.
    Decoded {
        /// Borrowed result storage; reuse requires dropping the report.
        ids: &'a [u64],
    },
    /// No provisional IDs escape this row.
    Failed {
        /// Algebraic failure within a request that completed successfully.
        reason: DecodeFailure,
    },
}

/// Atomic request result, borrowing preallocated output storage in bucket order.
#[derive(Debug)]
pub struct DecodeReport<'s> {
    outcomes: &'s [StoredOutcome],
    ids: &'s [u64],
    /// Deterministic request-wide logical work.
    pub work: WorkUnits,
    /// Peak required arena size; unused reusable capacity is excluded.
    pub peak_scratch_bytes: usize,
}

impl DecodeReport<'_> {
    #[cfg(test)]
    pub(super) fn result_offsets(&self) -> Vec<(u64, u64)> {
        self.outcomes
            .iter()
            .map(|row| (row.start, row.len))
            .collect()
    }

    /// Number of admitted rows, including failed and equal rows.
    #[must_use]
    pub fn bucket_count(&self) -> usize {
        self.outcomes.len()
    }

    /// Read a completed row by bucket index.
    ///
    /// # Panics
    /// Only if internal publication invariants admit an unfinished or invalid row.
    #[must_use]
    #[inline(always)]
    pub fn outcome(&self, bucket: usize) -> Option<DecodeOutcome<'_>> {
        let row = self.outcomes.get(bucket)?;
        Some(match row.status {
            OutcomeStatus::Unset => panic!("unpublished row in a finished report"),
            OutcomeStatus::Equal => DecodeOutcome::Equal,
            OutcomeStatus::Decoded => {
                let start = usize::try_from(row.start).expect("admitted result offset");
                let len = usize::try_from(row.len).expect("admitted result length");
                DecodeOutcome::Decoded {
                    ids: &self.ids[start..start + len],
                }
            }
            OutcomeStatus::DegreeExceedsBudget => DecodeOutcome::Failed {
                reason: DecodeFailure::DegreeExceedsBudget,
            },
            OutcomeStatus::InvalidLocator => DecodeOutcome::Failed {
                reason: DecodeFailure::InvalidLocator,
            },
            OutcomeStatus::NotSplit => DecodeOutcome::Failed {
                reason: DecodeFailure::NotSplit,
            },
            OutcomeStatus::VerificationFailed => DecodeOutcome::Failed {
                reason: DecodeFailure::VerificationFailed,
            },
        })
    }
}

// Fixed-width metadata keeps scratch admission independent of pointer width/backend.
#[derive(Clone, Copy, Debug, Default)]
#[repr(u64)]
pub(crate) enum OutcomeStatus {
    #[default]
    Unset,
    Equal,
    Decoded,
    DegreeExceedsBudget,
    InvalidLocator,
    NotSplit,
    VerificationFailed,
}

#[derive(Clone, Copy, Debug, Default)]
#[repr(C)]
pub(crate) struct StoredOutcome {
    status: OutcomeStatus,
    start: u64,
    len: u64,
}

#[derive(Debug)]
pub(crate) struct AdmittedRequest {
    pub(crate) layout: ScratchLayout,
    pub(crate) meter: WorkMeter,
    pub(crate) zero_failures: usize,
}

/// Strict error precedence: shape, plan, candidates, work, then scratch. Preflight is bounded and allocation-free. Recomputing row
/// budgets avoids needing a temporary vector before scratch admission, including a short outcome segment.
pub(super) fn admit_request<F: BinaryField>(
    request: &impl RequestInput<F>,
    scratch: &DecodeScratch<F>,
) -> Result<AdmittedRequest, DecodeError> {
    request.validate_shape()?;
    let beta = request.limits().max_output_per_bucket;
    if !request.plan().is_supported()
        || (0..request.bucket_count()).any(|b| beta > request.capacity(b))
    {
        return Err(DecodeError::InvalidPlan);
    }
    let rows = || {
        (0..request.bucket_count()).map(|b| {
            (
                request.capacity(b),
                beta.checked_sub(usize::from(request.zero(b))),
            )
        })
    };
    let zero_failures = if beta == 0 {
        (0..request.bucket_count())
            .filter(|&b| request.zero(b))
            .count()
    } else {
        0
    };
    let candidates = request.candidate_count()?;
    if candidates > request.limits().max_candidate_inputs {
        return Err(DecodeError::CandidateLimitExceeded);
    }
    let cached_shape = request.cached_shape(beta);
    if request.plan().has_probes()
        && candidates == 0
        && beta == request.capacity(0)
        && let Some(shape) = cached_shape
        && let Some(layout) = scratch.no_hint_layout(shape, request.bucket_count(), *request.plan())
    {
        let mut meter = WorkMeter::new(request.limits().max_work);
        meter.charge(WorkScheduleV1::cost(Charge::Admission {
            rows: request.bucket_count(),
        })?)?;
        if layout.total_bytes() > request.limits().max_scratch_bytes || !scratch.covers(layout) {
            return Err(DecodeError::ScratchTooSmall);
        }
        return Ok(AdmittedRequest {
            layout: layout.clone(),
            meter,
            zero_failures,
        });
    }
    // Complete-bound overflow is rejected before work and scratch admission.
    request.plan().work_bound(rows(), beta, candidates)?;
    let mut meter = WorkMeter::new(request.limits().max_work);
    meter.charge(WorkScheduleV1::cost(Charge::Admission {
        rows: request.bucket_count(),
    })?)?;
    let layout = ScratchLayout::from_rows(rows(), beta, candidates)?;
    if layout.total_bytes() > request.limits().max_scratch_bytes || !scratch.covers(&layout) {
        return Err(DecodeError::ScratchTooSmall);
    }
    Ok(AdmittedRequest {
        layout,
        meter,
        zero_failures,
    })
}

#[cfg(test)]
pub(super) fn admit<F: BinaryField>(
    request: &DecodeRequest<'_, F>,
    scratch: &DecodeScratch<F>,
) -> Result<AdmittedRequest, DecodeError> {
    admit_request(request, scratch)
}

/// Only finish publishes. The job retains the disjoint workspace borrow, while
/// this result borrow transfers to the report and prevents premature arena reuse.
pub(crate) struct Publication<'s> {
    results: ResultStorage<'s>,
    rows: usize,
    written: usize,
    used_ids: usize,
    id_capacity: usize,
    failure: Option<DecodeError>,
}

impl<'s> Publication<'s> {
    #[inline(always)]
    pub(crate) fn new(results: ResultStorage<'s>, layout: &ScratchLayout) -> Self {
        assert!(
            results.ids.len() >= layout.result_ids && results.outcomes.len() >= layout.outcomes,
            "publication requires admitted results"
        );
        results.outcomes[..layout.outcomes].fill(StoredOutcome::default());
        Self {
            results,
            rows: layout.outcomes,
            written: 0,
            used_ids: 0,
            id_capacity: layout.result_ids,
            failure: None,
        }
    }

    /// Decoded IDs are verified nonzero roots; prepend original-ID zero when present.
    /// The returned row slice may occupy any workspace segment and is copied before reuse.
    #[inline(always)]
    pub(crate) fn write(&mut self, bucket: usize, outcome: DecodeOutcome<'_>, zero: bool) {
        assert!(self.failure.is_none(), "cannot write after request failure");
        assert!(
            bucket == self.written && bucket < self.rows,
            "rows must complete in bucket order"
        );
        let mut start = 0;
        let mut len = 0;
        let status = match outcome {
            DecodeOutcome::Equal => OutcomeStatus::Equal,
            DecodeOutcome::Failed { reason } => match reason {
                DecodeFailure::DegreeExceedsBudget => OutcomeStatus::DegreeExceedsBudget,
                DecodeFailure::InvalidLocator => OutcomeStatus::InvalidLocator,
                DecodeFailure::NotSplit => OutcomeStatus::NotSplit,
                DecodeFailure::VerificationFailed => OutcomeStatus::VerificationFailed,
            },
            DecodeOutcome::Decoded { ids } => {
                assert!(
                    (!ids.is_empty() || zero)
                        && ids.first() != Some(&0)
                        && ids.windows(2).all(|w| w[0] < w[1]),
                    "decoded roots must be nonzero and strictly ascending; output must be nonempty"
                );
                let prefix = usize::from(zero);
                let end = self
                    .used_ids
                    .checked_add(prefix)
                    .and_then(|start| start.checked_add(ids.len()))
                    .expect("admitted result offsets");
                assert!(end <= self.id_capacity, "admitted result storage exhausted");
                if zero {
                    self.results.ids[self.used_ids] = 0;
                }
                let destination = &mut self.results.ids[self.used_ids + prefix..end];
                match ids {
                    [id] => destination[0] = *id,
                    [first, second] => {
                        destination[0] = *first;
                        destination[1] = *second;
                    }
                    _ => destination.copy_from_slice(ids),
                }
                start = u64::try_from(self.used_ids).expect("result offset fits u64");
                len = u64::try_from(end - self.used_ids).expect("result length fits u64");
                self.used_ids = end;
                OutcomeStatus::Decoded
            }
        };
        self.results.outcomes[bucket] = StoredOutcome { status, start, len };
        self.written += 1;
    }

    pub(crate) fn fail(&mut self, error: DecodeError) {
        if self.failure.is_none() {
            self.failure = Some(error);
        }
    }

    #[inline(always)]
    pub(crate) fn finish(
        self,
        work: WorkUnits,
        peak: usize,
    ) -> Result<DecodeReport<'s>, DecodeError> {
        if let Some(error) = self.failure {
            return Err(error);
        }
        assert_eq!(
            self.written, self.rows,
            "finish requires every row to complete"
        );
        Ok(DecodeReport {
            outcomes: &self.results.outcomes[..self.rows],
            ids: &self.results.ids[..self.used_ids],
            work,
            peak_scratch_bytes: peak,
        })
    }
}
