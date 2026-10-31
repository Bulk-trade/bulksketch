//! Transactional whole-row degree-three/four probes. No candidate or splitter state.
#![forbid(unsafe_code)]
use {
    super::{
        deg34,
        probe::verified,
        row::RowBudget,
        scratch::RowWorkspace,
        work::{Charge, WorkScheduleV1},
    },
    crate::{
        backend::contract::BulkKernels,
        field::BinaryField,
        types::{DecodeError, Stage, WorkMeter},
    },
};

#[derive(Debug)]
pub(super) struct DegreeProbe {
    degree: u8,
    count: u8,
    next: Option<Stage>,
}
impl DegreeProbe {
    // Use every available check at c=3..6. Roots still need the product certificate
    // and complete row verification; no extra stored words are required.
    pub(super) fn new(budget: RowBudget, capacity: usize) -> Option<Self> {
        (budget.nonzero >= 3 && capacity >= 3).then_some(Self {
            degree: 3,
            count: 0,
            next: Some(Stage::GuardThree),
        })
    }
    pub(super) fn next_stage(&self) -> Option<Stage> {
        self.next
    }
    pub(super) fn count(&self) -> usize {
        usize::from(self.count)
    }
    pub(super) fn reject(&mut self, capacity: usize, budget: RowBudget) {
        self.count = 0;
        self.next = Some(
            if self.degree == 3 && capacity >= 4 && budget.nonzero >= 4 {
                self.degree = 4;
                Stage::GuardFour
            } else {
                Stage::Reconstruction
            },
        );
    }
    pub(super) fn run<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        odd: &[u64],
        budget: RowBudget,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Option<Stage>, DecodeError> {
        let stage = self.next.expect("active degree probe");
        let degree = usize::from(self.degree);
        let count = self.count();
        let operation = match stage {
            Stage::GuardThree => Charge::GuardThree,
            Stage::GuardFour => Charge::GuardFour,
            Stage::NewtonThree => Charge::NewtonThree,
            Stage::NewtonFour => Charge::NewtonFour,
            Stage::LeafThree => Charge::LeafThree,
            Stage::LeafFour => Charge::LeafFour,
            Stage::FactorVerification => Charge::FactorVerification { degree },
            Stage::Verification => Charge::Verify {
                capacity: odd.len(),
                output_budget: budget.total,
            },
            Stage::Canonicalization => Charge::Canonicalize { ids: budget.total },
            _ => unreachable!("whole-row degree probe stage"),
        };
        meter.charge(WorkScheduleV1::cost(operation)?)?;
        #[cfg(test)]
        crate::types::small_degree_observer::stage(stage, false);
        match stage {
            Stage::GuardThree | Stage::GuardFour => {
                if deg34::guard::<F, K>(odd, degree, &mut workspace.polynomials[5..11]) {
                    self.next = Some(if degree == 3 {
                        Stage::NewtonThree
                    } else {
                        Stage::NewtonFour
                    });
                } else {
                    self.reject(odd.len(), budget);
                }
            }
            Stage::NewtonThree | Stage::NewtonFour => {
                let (factor, rest) = workspace.polynomials.split_at_mut(5);
                deg34::normalize::<F, K>(&rest[..6], odd[0], degree, factor);
                self.next = Some(if degree == 3 {
                    Stage::LeafThree
                } else {
                    Stage::LeafFour
                });
            }
            Stage::LeafThree | Stage::LeafFour => {
                let (factor, rest) = workspace.polynomials.split_at_mut(11);
                if let Some(count) = deg34::solve::<F, K>(&factor[..=degree], &mut rest[..4]) {
                    self.count = u8::try_from(count).expect("degree-three/four root count");
                    self.next = Some(Stage::FactorVerification);
                } else {
                    self.reject(odd.len(), budget);
                }
            }
            Stage::FactorVerification => {
                let (values, product) = workspace.polynomials.split_at_mut(15);
                let valid = deg34::certificate::<F, K>(
                    &values[..=degree],
                    &values[11..11 + count],
                    &mut product[..5],
                );
                #[cfg(test)]
                crate::types::small_degree_observer::certificate(valid);
                if valid {
                    workspace.roots[..count].copy_from_slice(&values[11..11 + count]);
                    self.next = Some(Stage::Verification);
                } else {
                    self.reject(odd.len(), budget);
                }
            }
            Stage::Verification => {
                if verified::<F, K>(odd, &workspace.roots[..count], workspace.verification) {
                    self.next = Some(Stage::Canonicalization);
                } else {
                    self.reject(odd.len(), budget);
                }
            }
            Stage::Canonicalization => {
                workspace.roots[..count].sort_unstable();
                self.next = None;
            }
            _ => unreachable!("charged degree probe"),
        }
        Ok(self.next)
    }
}
