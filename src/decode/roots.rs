//! Depth-first factor traversal; pending factors own coefficients, never parent tables.
#![forbid(unsafe_code)]
use {
    super::{
        affine, deg34,
        scratch::{FactorFrame, RowWorkspace, SplitterBasis},
        work::{Charge, WorkScheduleV1},
    },
    crate::{
        backend::contract::BulkKernels,
        field::BinaryField,
        poly::{Dense, Polynomial},
        types::{DecodeError, DecodeFailure, RawProduct, Stage, WorkMeter},
    },
};

#[derive(Debug, Default)]
pub(super) struct Roots {
    pending: usize,
    stride: usize,
    degree: usize,
    direction: u32,
    checked: bool,
    trace_len: usize,
    gcd_len: usize,
    pub(super) count: usize,
    pub(super) attempts: usize,
    pub(super) gcd_degree: usize,
    splitter_seed: u64,
    v3: bool,
    closed_form: bool,
    solved_count: usize,
    affine: bool,
    affine_ready: bool,
    affine_base: u64,
    affine_rank: usize,
}
// At degree d>=3 these regions need 7d+10 words, at most 8(r+1).
struct FactorWork<'a> {
    modulus: &'a mut [u64],
    trace: &'a mut [u64],
    gcd: &'a mut [u64],
    work: &'a mut [u64],
    table: &'a mut [u64],
    raw: &'a mut [RawProduct],
    basis: &'a mut SplitterBasis,
}
impl<'a> FactorWork<'a> {
    fn new(
        degree: usize,
        polynomials: &'a mut [u64],
        table: &'a mut [u64],
        raw: &'a mut [RawProduct],
        basis: &'a mut SplitterBasis,
    ) -> Self {
        let (modulus, rest) = polynomials.split_at_mut(degree + 1);
        let (trace, rest) = rest.split_at_mut(degree);
        let (gcd, work) = rest.split_at_mut(degree + 1);
        Self {
            modulus,
            trace,
            gcd,
            work,
            table: &mut table[..degree * (degree / 2)],
            raw,
            basis,
        }
    }
}
fn charge(meter: &mut WorkMeter, operation: Charge) -> Result<(), DecodeError> {
    meter.charge(WorkScheduleV1::cost(operation)?)
}
impl Roots {
    pub(super) fn enable_v3(&mut self) {
        self.v3 = true;
    }

    pub(super) fn enable_closed_form(&mut self) {
        self.closed_form = true;
    }

    pub(super) fn set_splitter_seed(&mut self, seed: u64) {
        self.splitter_seed = seed;
    }

    pub(super) fn start(&mut self, degree: usize, workspace: &mut RowWorkspace<'_>) -> Stage {
        // The cache belongs to this row, even when the scratch owner is reused.
        workspace.basis.directions = None;
        workspace.basis.len = 0;
        self.degree = degree;
        self.stride = degree + 1;
        self.affine = self.v3 && affine::preferred::<crate::field::Gf64>(degree);
        self.affine_ready = false;
        if degree != 0 {
            workspace.polynomials[..=degree].copy_from_slice(&workspace.bm[..=degree]);
        }
        self.stage()
    }
    fn stage(&self) -> Stage {
        if self.degree < 3 {
            Stage::Leaf
        } else if self.closed_form && self.degree == 3 {
            Stage::LeafThree
        } else if self.closed_form && self.degree == 4 {
            Stage::LeafFour
        } else {
            Stage::ReducerPreparation
        }
    }
    fn advance(&mut self, workspace: &mut RowWorkspace<'_>) -> Stage {
        if self.pending == 0 {
            return Stage::Verification;
        }
        self.pending -= 1;
        let frame = &workspace.stack[self.pending];
        let start = usize::try_from(frame.coefficient_start).expect("admitted coefficient offset");
        let len = usize::try_from(frame.coefficient_len).expect("admitted coefficient length");
        workspace.polynomials[..len].copy_from_slice(&workspace.factors[start..start + len]);
        self.degree = len - 1;
        self.direction = frame.next_direction;
        self.checked = frame.split_checked != 0;
        if self.affine {
            self.affine_base = workspace.factors[start + self.stride - 1];
            self.affine_rank = frame.next_direction as usize;
        }
        self.stage()
    }
    pub(super) fn run<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        stage: Stage,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        #[cfg(test)]
        crate::types::small_degree_observer::stage(stage, true);
        if matches!(
            stage,
            Stage::LeafThree | Stage::LeafFour | Stage::FactorVerification
        ) {
            return self.closed_leaf::<F, K>(stage, workspace, meter);
        }
        if stage == Stage::Leaf {
            return self.leaf::<F, K>(workspace, meter);
        }
        if stage == Stage::AffinePreparation {
            return self.prepare_affine::<F, K>(workspace, meter);
        }
        if stage == Stage::AffineEnumeration {
            return self.enumerate_affine::<F, K>(workspace, meter);
        }
        let degree = self.degree;
        let mut buffers = FactorWork::new(
            degree,
            workspace.polynomials,
            workspace.square_table,
            workspace.raw,
            workspace.basis,
        );
        match stage {
            Stage::ReducerPreparation => {
                charge(meter, Charge::Table { degree })?;
                <Dense as Polynomial<F, K>>::prepare_square_table(
                    buffers.modulus,
                    buffers.table,
                    buffers.work,
                );
                Ok(Ok(if self.affine {
                    if self.affine_ready {
                        Stage::AffineSplit
                    } else {
                        Stage::AffinePreparation
                    }
                } else {
                    Stage::Trace
                }))
            }
            Stage::AffineSplit => {
                charge(
                    meter,
                    Charge::AffineSplit {
                        degree,
                        rank: self.affine_rank,
                    },
                )?;
                if self.affine_rank == 0 {
                    return Ok(Err(DecodeFailure::NotSplit));
                }
                let rank = self.affine_rank - 1;
                let start = self.stride * self.stride + affine::subspace_start(rank);
                self.trace_len = affine::splitter::<F, K>(
                    buffers.modulus,
                    buffers.table,
                    &workspace.factors[start..start + rank + 1],
                    self.affine_base,
                    buffers.trace,
                    buffers.work,
                    buffers.raw,
                );
                Ok(Ok(Stage::Gcd))
            }
            Stage::Trace => self.trace::<F, K>(&mut buffers, meter),
            Stage::Gcd => {
                charge(meter, Charge::Gcd { degree })?;
                self.gcd_len = <Dense as Polynomial<F, K>>::monic_gcd_into(
                    buffers.modulus,
                    &buffers.trace[..self.trace_len],
                    buffers.gcd,
                    buffers.work,
                    buffers.raw,
                );
                self.gcd_degree = self.gcd_len - 1;
                if self.gcd_degree > 0 && self.gcd_degree < degree {
                    return Ok(Ok(Stage::FactorDivision));
                }
                if self.affine {
                    self.affine_rank -= 1;
                    if self.gcd_len == 1 {
                        self.affine_base ^=
                            buffers.basis.directions.as_ref().expect("affine basis")
                                [self.affine_rank];
                    }
                    return Ok(Ok(Stage::AffineSplit));
                }
                self.direction += 1;
                if self.direction == F::BITS {
                    Ok(Err(DecodeFailure::NotSplit))
                } else {
                    Ok(Ok(Stage::Trace))
                }
            }
            Stage::FactorDivision => {
                self.divide::<F, K>(&mut buffers, workspace.factors, workspace.stack, meter)
            }
            _ => unreachable!("root traversal stage"),
        }
    }
    fn closed_leaf<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        stage: Stage,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        let degree = self.degree;
        if stage != Stage::FactorVerification {
            charge(
                meter,
                if degree == 3 {
                    Charge::LeafThree
                } else {
                    Charge::LeafFour
                },
            )?;
            let (factor, rest) = workspace.polynomials.split_at_mut(11);
            let Some(count) = deg34::solve::<F, K>(&factor[..=degree], &mut rest[..4]) else {
                return Ok(Ok(Stage::ReducerPreparation));
            };
            self.solved_count = count;
            return Ok(Ok(Stage::FactorVerification));
        }
        charge(meter, Charge::FactorVerification { degree })?;
        let (values, product) = workspace.polynomials.split_at_mut(15);
        let roots = &values[11..11 + self.solved_count];
        let valid = deg34::certificate::<F, K>(&values[..=degree], roots, &mut product[..5]);
        #[cfg(test)]
        crate::types::small_degree_observer::certificate(valid);
        if !valid {
            return Ok(Ok(Stage::ReducerPreparation));
        }
        workspace.roots[self.count..self.count + degree].copy_from_slice(roots);
        self.count += degree;
        Ok(Ok(self.advance(workspace)))
    }

    fn prepare_affine<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        let degree = self.degree;
        charge(meter, Charge::AffinePreparation { degree })?;
        let (coefficients, work) = workspace.bm.split_at_mut(degree + 1);
        let len = affine::multiple::<F, K>(
            &workspace.polynomials[..=degree],
            &workspace.square_table[..degree * (degree / 2)],
            workspace.factors,
            coefficients,
            work,
            workspace.raw,
        );
        // The X coefficient is the affine multiple's constant derivative.
        // A repeated factor forces it to zero. Conversely, for a squarefree
        // input a zero derivative would give a smaller affine multiple by
        // taking a square root, contradicting minimality.
        if coefficients[1] == 0 {
            return Ok(Err(DecodeFailure::NotSplit));
        }
        let basis = workspace.basis.directions.insert([0; 64]);
        let Some((base, rank)) = affine::solve_map::<F, K>(&coefficients[..len], basis) else {
            return Ok(Err(DecodeFailure::NotSplit));
        };
        if rank >= len - 1
            || 1_u64
                .checked_shl(rank as u32)
                .is_some_and(|n| n < degree as u64)
        {
            return Ok(Err(DecodeFailure::NotSplit));
        }
        workspace.basis.len = rank as u32;
        self.affine_base = base;
        self.affine_rank = rank;
        self.affine_ready = true;
        if affine::enumerate_preferred(degree, rank) {
            Ok(Ok(Stage::AffineEnumeration))
        } else {
            let offset = self.stride * self.stride;
            affine::subspaces::<F, K>(&basis[..rank], &mut workspace.factors[offset..]);
            Ok(Ok(Stage::AffineSplit))
        }
    }

    fn enumerate_affine<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        charge(
            meter,
            Charge::AffineEnumeration {
                degree: self.degree,
                rank: self.affine_rank,
            },
        )?;
        let found = match affine::enumerate::<F, K>(
            &workspace.polynomials[..=self.degree],
            self.affine_base,
            &workspace.basis.directions.as_ref().expect("affine basis")[..self.affine_rank],
            &mut workspace.roots[self.count..],
            workspace.bm,
        ) {
            Ok(count) => count,
            Err(reason) => return Ok(Err(reason)),
        };
        self.count += found;
        Ok(Ok(self.advance(workspace)))
    }

    fn leaf<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        charge(
            meter,
            Charge::Leaf {
                degree: self.degree,
            },
        )?;
        let roots = match self.degree {
            0 => [0, 0],
            1 => [workspace.polynomials[0], 0],
            2 => {
                let linear = workspace.polynomials[1];
                if linear == 0 {
                    return Ok(Err(DecodeFailure::NotSplit));
                }
                let inverse = K::inverse(linear).expect("nonzero quadratic coefficient");
                let target = K::mul(workspace.polynomials[0], K::square(inverse));
                let Some(solution) = K::solve_quadratic(target) else {
                    return Ok(Err(DecodeFailure::NotSplit));
                };
                let root = K::mul(linear, solution);
                [root, root ^ linear]
            }
            _ => unreachable!("leaf degree at most two"),
        };
        if roots[..self.degree].contains(&0) {
            return Ok(Err(DecodeFailure::InvalidLocator));
        }
        workspace.roots[self.count..self.count + self.degree]
            .copy_from_slice(&roots[..self.degree]);
        self.count += self.degree;
        Ok(Ok(self.advance(workspace)))
    }
    fn trace<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        buffers: &mut FactorWork<'_>,
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        let degree = self.degree;
        charge(meter, Charge::Trace { degree })?;
        self.attempts += 1;
        let seed = self.splitter_seed;
        let basis_len = &mut buffers.basis.len;
        let basis = buffers.basis.directions.get_or_insert_with(|| {
            let mut basis = [0; 64];
            basis[0] = (seed & F::MASK).max(1);
            *basis_len = 1;
            basis
        });
        // Pending siblings can resume earlier directions. Retain the initialized
        // prefix, extending it only after the requested Trace has been charged.
        while *basis_len <= self.direction {
            let splitter = basis[*basis_len as usize - 1];
            let carry = splitter >> (F::BITS - 1);
            basis[*basis_len as usize] =
                ((splitter << 1) & F::MASK) ^ (F::MODULUS_LOW & 0u64.wrapping_sub(carry));
            *basis_len += 1;
        }
        let splitter = basis[self.direction as usize];
        buffers.trace.fill(0);
        buffers.trace[1] = splitter;
        self.trace_len = 2;
        for _ in 1..F::BITS {
            let len = <Dense as Polynomial<F, K>>::square_mod_into(
                &buffers.trace[..self.trace_len],
                buffers.modulus,
                buffers.table,
                buffers.gcd,
                buffers.raw,
            );
            buffers.trace[..len].copy_from_slice(&buffers.gcd[..len]);
            self.trace_len =
                <Dense as Polynomial<F, K>>::xor_coefficient(buffers.trace, len, 1, splitter);
        }
        if !self.checked {
            charge(meter, Charge::SplitCheck { degree })?;
            <Dense as Polynomial<F, K>>::square_mod_into(
                &buffers.trace[..self.trace_len],
                buffers.modulus,
                buffers.table,
                buffers.gcd,
                buffers.raw,
            );
            // Modular squaring writes all d output words. Pad the normalized trace
            // to compare T^2+T, including coefficients above either normalized end.
            buffers.trace[self.trace_len..].fill(0);
            if buffers.gcd[..degree] != *buffers.trace {
                return Ok(Err(DecodeFailure::NotSplit));
            }
            self.checked = true;
        }
        Ok(Ok(Stage::Gcd))
    }
    fn divide<F: BinaryField, K: BulkKernels<F>>(
        &mut self,
        buffers: &mut FactorWork<'_>,
        factors: &mut [u64],
        stack: &mut [FactorFrame],
        meter: &mut WorkMeter,
    ) -> Result<Result<Stage, DecodeFailure>, DecodeError> {
        let degree = self.degree;
        charge(meter, Charge::Divide { degree })?;
        let (quotient, remainder) = buffers.work.split_at_mut(degree + 2);
        let Some(len) = <Dense as Polynomial<F, K>>::exact_divide_into(
            buffers.modulus,
            &buffers.gcd[..self.gcd_len],
            quotient,
            remainder,
            buffers.raw,
        ) else {
            return Ok(Err(DecodeFailure::InvalidLocator));
        };
        charge(meter, Charge::SplitAssembly { degree })?;
        // The pending right child owns coefficients only. The left replaces the
        // modulus; no released parent reducer can ever be resumed.
        let start = self
            .pending
            .checked_mul(self.stride)
            .ok_or(DecodeError::ScratchTooSmall)?;
        let end = start.checked_add(len).ok_or(DecodeError::ScratchTooSmall)?;
        factors[start..end].copy_from_slice(&quotient[..len]);
        stack[self.pending] = FactorFrame {
            coefficient_start: u64::try_from(start).expect("admitted offset"),
            coefficient_len: u64::try_from(len).expect("admitted degree"),
            next_direction: self.direction + 1,
            split_checked: 1,
        };
        if self.affine {
            self.affine_rank -= 1;
            factors[start + self.stride - 1] = self.affine_base
                ^ buffers.basis.directions.as_ref().expect("affine basis")[self.affine_rank];
            stack[self.pending].next_direction = self.affine_rank as u32;
        }
        self.pending += 1;
        buffers.modulus[..self.gcd_len].copy_from_slice(&buffers.gcd[..self.gcd_len]);
        self.degree = self.gcd_degree;
        self.direction += 1;
        self.checked = true;
        Ok(Ok(self.stage()))
    }
}
#[cfg(test)]
mod trace_tests;

#[cfg(test)]
mod affine_tests;
