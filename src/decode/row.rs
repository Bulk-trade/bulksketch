//! Staged ordinary binary rows. Mapping and zero stay upstairs.
#![forbid(unsafe_code)]

use {
    super::scratch::RowWorkspace,
    crate::{
        backend::contract::BulkKernels,
        field::BinaryField,
        types::{DecodeError, DecodeFailure, Stage, WorkMeter},
    },
};

/// Field roots only: distinct, nonzero, ascending, count <= the checked nonzero budget.
/// Decoded borrows exactly the verified roots from any workspace segment; no prefix
/// location is promised. The upper job copies this slice and prepends original zero.
pub(crate) enum RowResult<'w> {
    Equal,
    Decoded(&'w [u64]),
    Failed(DecodeFailure),
}

/// Checked upstairs: nonzero <= total <= capacity, with at most one zero slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RowBudget {
    pub(crate) nonzero: usize,
    pub(crate) total: usize,
}

/// Canonical odd difference and normalized nonzero hints, unchanged across stages.
#[derive(Clone, Copy, Debug)]
pub(crate) struct RowInput<'a> {
    pub(crate) difference: &'a [u64],
    pub(crate) candidates: &'a [u64],
}

/// Row-local progress. The request job adds bucket, request work and complete arena size;
/// lower code never constructs the public job's request-level progress record.
pub(crate) struct RowProgress {
    pub(crate) stage: Stage,
    pub(crate) locator_degree: usize,
    pub(crate) candidate_hits: usize,
    pub(crate) trace_attempts: usize,
    pub(crate) gcd_degree: usize,
}

/// Execution owns only small row state, never borrowed inputs or workspace handles.
/// Progress exposes no provisional roots. V2's private upper-job handoff validates
/// proposed roots before canonicalization; rejection resumes the row without publication.
/// Finish drains and borrows only completed roots.
pub(crate) trait RowExecution {
    fn next_stage(&self) -> Option<Stage>;
    fn run_next(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowProgress, DecodeError>;
    /// Drain and consume execution; only a completed, verified slice may escape.
    /// Its borrow ends before workspace reuse; callers must use the returned slice,
    /// not infer a storage location. Drop and errors publish no roots.
    #[cfg_attr(
        not(test),
        allow(
            dead_code,
            reason = "The consuming row contract is tested directly; request jobs borrow \
                      completed rows"
        )
    )]
    fn finish<'w>(
        self,
        input: RowInput<'_>,
        workspace: &'w mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowResult<'w>, DecodeError>;
}

/// One monomorphized row driver per arithmetic capability; no runtime per-multiply dispatch.
pub(crate) trait RowDecoder<F: BinaryField, K: BulkKernels<F>> {
    type Execution: RowExecution;
    /// difference.len=c>0; budgets checked; hints normalized/nonzero/canonical.
    /// Each stage is lent the same row segments; no stage may grow them.
    /// Reject BM degree beyond budget.nonzero before out-of-budget writes.
    /// Verification and canonicalization charge budget.total, including the zero slot.
    /// General stages retain V1 charges. V2 probes pay before materialization/algebra
    /// and each verification; misses preserve these inputs and fresh general state.
    /// V3 may replace roots/verification with charged affine and rebuilt-LFSR stages.
    fn begin(budget: RowBudget) -> Self::Execution;
}
