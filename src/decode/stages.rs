//! The row owns counters and stage state; every coefficient stays in the lent workspace.
#![forbid(unsafe_code)]
#[cfg(test)]
use super::{direct, probe::Probe};
use {
    super::{
        bm,
        degree_probe::DegreeProbe,
        probe::verified,
        roots::Roots,
        row::{RowBudget, RowDecoder, RowExecution, RowInput, RowProgress, RowResult},
        scratch::RowWorkspace,
        verify,
        work::{Charge, WorkScheduleV1},
    },
    crate::{
        backend::contract::BulkKernels,
        field::BinaryField,
        poly::{Dense, Polynomial},
        types::{DecodeError, DecodeFailure, Stage, WorkMeter},
    },
    std::marker::PhantomData,
};

#[derive(Clone, Copy, Debug)]
pub(crate) struct BinaryDecoder;
#[derive(Debug)]
enum State {
    Running(Stage),
    Complete,
    Failed(DecodeFailure),
    Error(DecodeError),
}

#[derive(Debug)]
pub(crate) struct Execution<F, K> {
    budget: RowBudget,
    state: State,
    degree: usize,
    hits: usize,
    roots: Roots,
    v3: bool,
    degree_probe: Option<DegreeProbe>,
    #[cfg(test)]
    probe: Option<Probe>,
    #[cfg(test)]
    pub(crate) probe_algebra: Option<(u64, u64, u64)>,
    #[cfg(test)]
    pub(crate) probe_fault: direct::Fault,
    #[cfg(test)]
    pub(crate) operation_observer: Option<std::sync::Arc<std::sync::atomic::AtomicUsize>>,
    marker: PhantomData<(F, K)>,
}
impl<F: BinaryField, K: BulkKernels<F>> RowDecoder<F, K> for BinaryDecoder {
    type Execution = Execution<F, K>;
    fn begin(budget: RowBudget) -> Self::Execution {
        Execution {
            budget,
            state: State::Running(Stage::Reconstruction),
            degree: 0,
            hits: 0,
            roots: Roots::default(),
            v3: false,
            degree_probe: None,
            #[cfg(test)]
            probe: None,
            #[cfg(test)]
            probe_algebra: None,
            #[cfg(test)]
            probe_fault: direct::Fault::None,
            #[cfg(test)]
            operation_observer: None,
            marker: PhantomData,
        }
    }
}
impl<F: BinaryField, K: BulkKernels<F>> Execution<F, K> {
    #[cfg(test)]
    pub(crate) fn provisional_count(&self) -> usize {
        self.roots.count
    }

    #[cfg(test)]
    fn observe_operation(&self) {
        if let Some(counter) = &self.operation_observer {
            // Each test observes entries on its own thread; no synchronization is needed.
            counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
    }
    /// A new row has the same backend but no retained counters, probes or traversal state.
    #[inline(always)]
    pub(crate) fn restart(&mut self, budget: RowBudget, seed: u64) {
        *self = <BinaryDecoder as RowDecoder<F, K>>::begin(budget);
        self.set_splitter_seed(seed);
    }

    pub(crate) fn enable_v3(&mut self) {
        self.v3 = true;
        self.roots.enable_v3();
        if F::BITS == 64 {
            self.roots.enable_closed_form();
        }
    }

    /// Called only for a genuinely different row, after tiny probes miss/skip.
    pub(crate) fn start_degrees(&mut self, capacity: usize) {
        if self.v3 && F::BITS == 64 {
            self.degree_probe = DegreeProbe::new(self.budget, capacity);
            if let Some(probe) = &self.degree_probe {
                self.state = State::Running(probe.next_stage().expect("new degree probe"));
            }
        }
    }

    pub(crate) fn verification_count(&self) -> usize {
        self.roots.count
    }

    /// Upper validation is part of Verification, before any canonicalization.
    pub(crate) fn reject_upper(&mut self, capacity: usize) {
        if let Some(probe) = &mut self.degree_probe {
            probe.reject(capacity, self.budget);
            self.roots.count = 0;
            self.state = State::Running(probe.next_stage().expect("probe fallback"));
            if probe.next_stage() == Some(Stage::Reconstruction) {
                self.degree_probe = None;
            }
        } else {
            self.state = State::Failed(DecodeFailure::InvalidLocator);
        }
    }

    #[cfg(test)]
    pub(crate) fn start_probes(&mut self, difference: &[u64]) {
        self.probe = Probe::new(self.budget, difference);
        if let Some(probe) = &self.probe {
            self.state = State::Running(probe.next_stage().expect("new probe"));
        }
    }

    /// Borrow only an already completed row; the upper job has drained its stages.
    pub(crate) fn completed_result<'w>(
        &self,
        workspace: &'w RowWorkspace<'_>,
    ) -> Result<RowResult<'w>, DecodeError> {
        match self.state {
            State::Error(error) => return Err(error),
            State::Failed(reason) => return Ok(RowResult::Failed(reason)),
            State::Complete => {}
            State::Running(_) => unreachable!("drained execution"),
        }
        if self.roots.count == 0 && self.budget.total == self.budget.nonzero {
            Ok(RowResult::Equal)
        } else {
            Ok(RowResult::Decoded(&workspace.roots[..self.roots.count]))
        }
    }

    pub(crate) fn set_splitter_seed(&mut self, seed: u64) {
        self.roots.set_splitter_seed(seed);
    }

    fn charge(meter: &mut WorkMeter, operation: Charge) -> Result<(), DecodeError> {
        meter.charge(WorkScheduleV1::cost(operation)?)
    }
    fn execute(
        &mut self,
        stage: Stage,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Option<Stage>, DecodeFailure>, DecodeError> {
        let capacity = input.difference.len();
        #[cfg(test)]
        crate::types::small_degree_observer::stage(stage, false);
        if let Some(probe) = &mut self.degree_probe {
            let next = probe.run::<F, K>(input.difference, self.budget, workspace, meter)?;
            self.roots.count = probe.count();
            if next == Some(Stage::Reconstruction) {
                self.degree_probe = None;
            }
            return Ok(Ok(next));
        }
        #[cfg(test)]
        if let Some(probe) = &mut self.probe {
            // Lower-layer callers use the same probe stages as the public job.
            #[cfg(test)]
            {
                probe.probe_fault = self.probe_fault;
                probe
                    .operation_observer
                    .clone_from(&self.operation_observer);
            }
            // Standalone row callers do not have request-wide scratch admission.
            probe.charge(capacity, meter)?;
            if matches!(stage, Stage::DirectOne | Stage::DirectTwo) {
                check_workspace(workspace, capacity, self.budget.nonzero)?;
            }
            let progress = probe.run_charged::<F, K>(
                input.difference,
                workspace.verification,
                workspace.roots,
            );
            debug_assert_eq!(progress.stage, stage);
            self.roots.count = probe.count();
            #[cfg(test)]
            {
                self.probe_algebra = probe.probe_algebra;
            }
            let next = probe.next_stage();
            if next == Some(Stage::Reconstruction) {
                self.probe = None;
            }
            return Ok(Ok(next));
        }
        match stage {
            Stage::Reconstruction => self.reconstruct(input, workspace, meter),
            Stage::BerlekampMassey => {
                self.degree = match bm::locator::<F, K>(
                    workspace.syndromes,
                    capacity,
                    self.budget.nonzero,
                    workspace.bm,
                    meter,
                )? {
                    Ok(d) => d,
                    Err(e) => return Ok(Err(e)),
                };
                if workspace.bm[0] == 0 {
                    return Ok(Err(DecodeFailure::InvalidLocator));
                }
                Ok(Ok(Some(Stage::CandidateEvaluation)))
            }
            Stage::CandidateEvaluation => self.candidates(input, workspace, meter),
            Stage::Deflation => self.deflate(input, workspace, meter),
            Stage::Verification => self.verify(input, workspace, meter),
            Stage::Canonicalization => self.canonicalize(workspace, meter),
            _ => Ok(self.roots.run::<F, K>(stage, workspace, meter)?.map(Some)),
        }
    }
    fn reconstruct(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Option<Stage>, DecodeFailure>, DecodeError> {
        let capacity = input.difference.len();
        if self.budget.total == self.budget.nonzero
            && input.difference.iter().all(|&value| value == 0)
        {
            meter.charge(crate::types::WorkUnits(0))?;
            return Ok(Ok(None));
        }
        Self::charge(meter, Charge::Reconstruct { capacity })?;
        check_workspace(workspace, capacity, self.budget.nonzero)?;
        workspace.syndromes[0] = 0;
        for i in 1..=2 * capacity {
            workspace.syndromes[i] = if i.is_multiple_of(2) {
                K::square(workspace.syndromes[i / 2])
            } else {
                input.difference[i / 2]
            };
        }
        Ok(Ok(Some(Stage::BerlekampMassey)))
    }
    fn candidates(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Option<Stage>, DecodeFailure>, DecodeError> {
        let capacity = input.difference.len();
        Self::charge(
            meter,
            Charge::Candidates {
                degree: self.degree,
                inputs: input.candidates.len(),
            },
        )?;
        // The BM save buffer is free now; chunking bounds evaluation storage
        // independently of the number of normalized candidate hints.
        let width = capacity + 1;
        let (locator, rest) = workspace.bm.split_at_mut(width);
        let values = &mut rest[..width];
        for points in input.candidates.chunks(width) {
            <Dense as Polynomial<F, K>>::eval_many_into(
                &locator[..=self.degree],
                points,
                &mut values[..points.len()],
            );
            for (&point, &value) in points.iter().zip(values.iter()) {
                if value == 0 {
                    if self.hits == self.degree {
                        return Ok(Err(DecodeFailure::InvalidLocator));
                    }
                    workspace.roots[self.hits] = point;
                    self.hits += 1;
                }
            }
        }
        self.roots.count = self.hits;
        Ok(Ok(Some(Stage::Deflation)))
    }
    fn deflate(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Option<Stage>, DecodeFailure>, DecodeError> {
        let capacity = input.difference.len();
        Self::charge(
            meter,
            Charge::Deflate {
                degree: self.degree,
            },
        )?;
        let width = capacity + 1;
        let (locator, rest) = workspace.bm.split_at_mut(width);
        let quotient = &mut rest[..width];
        let mut degree = self.degree;
        for &root in &workspace.roots[..self.hits] {
            quotient[degree - 1] = locator[degree];
            for i in (1..degree).rev() {
                quotient[i - 1] = locator[i] ^ K::mul(root, quotient[i]);
            }
            if locator[0] ^ K::mul(root, quotient[0]) != 0 {
                return Ok(Err(DecodeFailure::InvalidLocator));
            }
            locator[..degree].copy_from_slice(&quotient[..degree]);
            degree -= 1;
        }
        Ok(Ok(Some(self.roots.start(degree, workspace))))
    }
    fn verify(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Option<Stage>, DecodeFailure>, DecodeError> {
        let capacity = input.difference.len();
        let lfsr = self.v3 && verify::use_rebuilt_lfsr(self.roots.count, capacity);
        let operation = if lfsr {
            Charge::VerifyLfsr {
                capacity,
                output_budget: self.budget.total,
                degree: self.roots.count,
            }
        } else {
            Charge::Verify {
                capacity,
                output_budget: self.budget.total,
            }
        };
        Self::charge(meter, operation)?;
        #[cfg(test)]
        self.observe_operation();
        let roots = &workspace.roots[..self.roots.count];
        let valid = if lfsr {
            verify::rebuilt_lfsr::<F, K>(
                roots,
                input.difference,
                workspace.bm,
                workspace.verification,
            )
        } else {
            verified::<F, K>(input.difference, roots, workspace.verification)
        };
        if !valid {
            return Ok(Err(DecodeFailure::VerificationFailed));
        }
        Ok(Ok(Some(Stage::Canonicalization)))
    }
    fn canonicalize(
        &mut self,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Option<Stage>, DecodeFailure>, DecodeError> {
        Self::charge(
            meter,
            Charge::Canonicalize {
                ids: self.budget.total,
            },
        )?;
        #[cfg(test)]
        self.observe_operation();
        if self.roots.count > self.budget.nonzero {
            return Ok(Err(DecodeFailure::DegreeExceedsBudget));
        }
        let roots = &mut workspace.roots[..self.roots.count];
        match roots {
            [left, right] => {
                if *left > *right {
                    std::mem::swap(left, right);
                }
            }
            [] | [_] => {}
            _ => roots.sort_unstable(),
        }
        if roots.iter().any(|&root| root == 0 || root & !F::MASK != 0)
            || roots.windows(2).any(|pair| pair[0] == pair[1])
        {
            return Ok(Err(DecodeFailure::InvalidLocator));
        }
        Ok(Ok(None))
    }
}
impl<F: BinaryField, K: BulkKernels<F>> RowExecution for Execution<F, K> {
    fn next_stage(&self) -> Option<Stage> {
        match self.state {
            State::Running(stage) => Some(stage),
            _ => None,
        }
    }
    fn run_next(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowProgress, DecodeError> {
        let stage = match self.state {
            State::Running(stage) => stage,
            State::Error(error) => return Err(error),
            _ => panic!("unfinished row"),
        };
        self.state = match self.execute(stage, input, workspace, meter) {
            Ok(Ok(Some(next))) => State::Running(next),
            Ok(Ok(None)) => State::Complete,
            Ok(Err(reason)) => State::Failed(reason),
            Err(error) => {
                self.state = State::Error(error);
                return Err(error);
            }
        };
        Ok(RowProgress {
            stage,
            locator_degree: self.degree,
            candidate_hits: self.hits,
            trace_attempts: self.roots.attempts,
            gcd_degree: self.roots.gcd_degree,
        })
    }
    fn finish<'workspace>(
        mut self,
        input: RowInput<'_>,
        workspace: &'workspace mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowResult<'workspace>, DecodeError> {
        while self.next_stage().is_some() {
            self.run_next(input, workspace, meter)?;
        }
        self.completed_result(workspace)
    }
}
fn check_workspace(
    workspace: &RowWorkspace<'_>,
    capacity: usize,
    budget: usize,
) -> Result<(), DecodeError> {
    let add = |a: usize, b: usize| a.checked_add(b).ok_or(DecodeError::ScratchTooSmall);
    let mul = |a: usize, b: usize| a.checked_mul(b).ok_or(DecodeError::ScratchTooSmall);
    let width = add(budget, 1)?;
    let polynomials = if budget == 0 { 0 } else { mul(8, width)? };
    let factors = if budget == 0 {
        0
    } else {
        mul(2, mul(width, width)?)?
    };
    let raw = if budget == 0 {
        0
    } else {
        mul(2, add(budget, 2)?)?
    };
    if workspace.syndromes.len() < add(mul(2, capacity)?, 1)?
        || workspace.bm.len() < mul(4, add(capacity, 1)?)?
        || workspace.polynomials.len() < polynomials
        || workspace.factors.len() < factors
        || workspace.square_table.len() < mul(budget, budget / 2)?
        || workspace.verification.len() < capacity
        || workspace.roots.len() < budget
        || workspace.raw.len() < raw
        || workspace.stack.len() < budget
    {
        Err(DecodeError::ScratchTooSmall)
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod direct_tests;

#[cfg(test)]
mod fallback_tests;
