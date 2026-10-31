//! Small V2 stage state. A miss resumes the general decoder at Reconstruction.
#![forbid(unsafe_code)]

use {
    super::{
        direct,
        row::{RowBudget, RowProgress},
        work::{Charge, WorkScheduleV1},
    },
    crate::{
        backend::contract::BulkKernels,
        field::BinaryField,
        types::{DecodeError, Stage, WorkMeter},
    },
};

#[derive(Debug)]
pub(crate) struct Probe {
    budget: RowBudget,
    next: Option<Stage>,
    count: usize,
    pair: bool,
    #[cfg(test)]
    pub(crate) probe_fault: direct::Fault,
    #[cfg(test)]
    pub(crate) probe_algebra: Option<(u64, u64, u64)>,
    #[cfg(test)]
    pub(crate) operation_observer: Option<std::sync::Arc<std::sync::atomic::AtomicUsize>>,
}

impl Probe {
    pub(crate) fn new(budget: RowBudget, difference: &[u64]) -> Option<Self> {
        (budget.nonzero != 0 && difference[0] != 0).then_some(Self {
            budget,
            next: Some(Stage::DirectOne),
            count: 0,
            pair: false,
            #[cfg(test)]
            probe_fault: direct::Fault::None,
            #[cfg(test)]
            probe_algebra: None,
            #[cfg(test)]
            operation_observer: None,
        })
    }

    pub(crate) fn next_stage(&self) -> Option<Stage> {
        self.next
    }
    pub(crate) fn count(&self) -> usize {
        self.count
    }
    #[cfg(test)]
    pub(crate) fn provisional_count(&self) -> usize {
        self.count
    }

    pub(crate) fn reject(&mut self, capacity: usize) {
        self.next = Some(if !self.pair && capacity >= 2 && self.budget.nonzero >= 2 {
            self.pair = true;
            Stage::DirectTwo
        } else {
            Stage::Reconstruction
        });
        self.count = 0;
    }

    #[inline(always)]
    pub(crate) fn run_next<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        difference: &[u64],
        verification: &mut [u64],
        roots: &mut [u64],
        meter: &mut WorkMeter,
    ) -> Result<RowProgress, DecodeError> {
        self.charge(difference.len(), meter)?;
        Ok(self.run_charged::<F, K>(difference, verification, roots))
    }

    // Standalone lower-layer executions validate their workspace between this
    // successful charge and run_charged. Public jobs already admitted the arena.
    #[inline(always)]
    pub(crate) fn charge(&self, capacity: usize, meter: &mut WorkMeter) -> Result<(), DecodeError> {
        let stage = self.next.expect("active probe");
        let charge = match stage {
            Stage::DirectOne => Charge::DirectOne,
            Stage::DirectTwo => Charge::DirectTwo,
            Stage::Verification => Charge::Verify {
                capacity,
                output_budget: self.budget.total,
            },
            Stage::Canonicalization => Charge::Canonicalize {
                ids: self.budget.total,
            },
            _ => unreachable!("probe has handed off to general execution"),
        };
        meter.charge(WorkScheduleV1::cost(charge)?)?;
        #[cfg(test)]
        if let Some(observer) = &self.operation_observer {
            observer.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        Ok(())
    }

    #[inline(always)]
    pub(crate) fn run_charged<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        difference: &[u64],
        verification: &mut [u64],
        roots: &mut [u64],
    ) -> RowProgress {
        let stage = self.next.expect("charged probe");
        match stage {
            Stage::DirectOne => {
                roots[0] = difference[0];
                self.count = 1;
                self.next = Some(Stage::Verification);
            }
            Stage::DirectTwo => {
                if let Some(pair) = direct::two::<F, K>(
                    difference[0],
                    difference[1],
                    #[cfg(test)]
                    self.probe_fault,
                ) {
                    roots[..2].copy_from_slice(&pair.roots);
                    self.count = 2;
                    #[cfg(test)]
                    {
                        self.probe_algebra = Some(pair.algebra);
                    }
                    self.next = Some(Stage::Verification);
                } else {
                    self.reject(difference.len());
                }
            }
            Stage::Verification => {
                let roots = &roots[..self.count];
                if roots.len() <= self.budget.nonzero
                    && roots.iter().all(|&id| id != 0 && id & !F::MASK == 0)
                    && !roots.windows(2).any(|p| p[0] == p[1])
                    && verified::<F, K>(difference, roots, verification)
                {
                    self.next = Some(Stage::Canonicalization);
                } else {
                    self.reject(difference.len());
                }
            }
            Stage::Canonicalization => {
                if self.count == 2 && roots[0] > roots[1] {
                    roots.swap(0, 1);
                }
                self.next = None;
            }
            _ => unreachable!("charged probe stage"),
        }
        RowProgress {
            stage,
            locator_degree: 0,
            candidate_hits: 0,
            trace_attempts: 0,
            gcd_degree: 0,
        }
    }
}

/// Called only after Verify is charged. Prefix rejection never replaces full re-encoding.
pub(super) fn verified<F: BinaryField, K: BulkKernels<F>>(
    difference: &[u64],
    roots: &[u64],
    verification: &mut [u64],
) -> bool {
    if roots.len() <= 2
        && (roots.iter().fold(0, |s, &x| s ^ x) != difference[0]
            || (difference.len() >= 2
                && roots.iter().fold(0, |s, &x| s ^ K::mul(x, K::square(x))) != difference[1]))
    {
        return false;
    }
    let verification = &mut verification[..difference.len()];
    K::encode_nonzero(verification, roots);
    verification == difference
}
