//! Contract composition with a known-singleton row driver, not a production solver.
#![forbid(unsafe_code)]

use {
    super::{
        api::{Publication, admit},
        scratch::RowLayout,
        *,
    },
    crate::{
        Gf64,
        backend::contract::{Arithmetic, BulkKernels},
        decode::{
            row::{RowBudget, RowDecoder, RowExecution, RowInput, RowProgress, RowResult},
            scratch::RowWorkspace,
            work::{Charge, WorkScheduleV1},
        },
        types::{DecodeError, DecodeFailure, RawProduct, Stage, WorkMeter, WorkUnits},
    },
};

#[derive(Clone, Copy)]
struct Reference;
impl Arithmetic<Gf64> for Reference {
    fn raw_mul(a: u64, b: u64) -> RawProduct {
        let mut product = 0u128;
        for bit in 0..64 {
            if b >> bit & 1 != 0 {
                product ^= u128::from(a) << bit;
            }
        }
        RawProduct {
            lo: u64::try_from(product & u128::from(u64::MAX)).unwrap(),
            hi: u64::try_from(product >> 64).unwrap(),
        }
    }
    fn reduce(product: RawProduct) -> u64 {
        let mut p = u128::from(product.lo) | (u128::from(product.hi) << 64);
        for bit in (64..128).rev() {
            if p >> bit & 1 != 0 {
                p ^= ((1u128 << 64) | 0x1b) << (bit - 64);
            }
        }
        u64::try_from(p).unwrap()
    }
    fn mul(a: u64, b: u64) -> u64 {
        Self::reduce(Self::raw_mul(a, b))
    }
    fn square(a: u64) -> u64 {
        Self::mul(a, a)
    }
    fn frobenius(mut a: u64, power: u32) -> u64 {
        for _ in 0..power % 64 {
            a = Self::square(a);
        }
        a
    }
    fn inverse(a: u64) -> Option<u64> {
        if a == 0 {
            return None;
        }
        let mut x = a;
        for _ in 1..63 {
            x = Self::mul(Self::square(x), a);
        }
        Some(Self::square(x))
    }
    fn trace(mut a: u64) -> u8 {
        let mut trace = 0;
        for _ in 0..64 {
            trace ^= a;
            a = Self::square(a);
        }
        u8::try_from(trace).unwrap()
    }
    fn solve_quadratic(a: u64) -> Option<u64> {
        let mut basis = [0u64; 64];
        let mut preimages = [0u64; 64];
        for bit in 0..64 {
            let mut preimage = 1u64 << bit;
            let mut column = Self::square(preimage) ^ preimage;
            for pivot in (0..64).rev() {
                if column >> pivot & 1 == 0 {
                    continue;
                }
                if basis[pivot] == 0 {
                    basis[pivot] = column;
                    preimages[pivot] = preimage;
                    break;
                }
                column ^= basis[pivot];
                preimage ^= preimages[pivot];
            }
        }
        let mut remainder = a;
        let mut result = 0;
        for pivot in (0..64).rev() {
            if remainder >> pivot & 1 != 0 {
                remainder ^= basis[pivot];
                result ^= preimages[pivot];
            }
        }
        (remainder == 0).then_some(result)
    }
    fn dot(a: &[u64], b: &[u64]) -> u64 {
        assert_eq!(a.len(), b.len());
        a.iter()
            .zip(b)
            .fold(0, |sum, (&a, &b)| sum ^ Self::mul(a, b))
    }
    fn scale_xor(dst: &mut [u64], src: &[u64], scale: u64) {
        assert_eq!(dst.len(), src.len());
        for (d, &s) in dst.iter_mut().zip(src) {
            *d ^= Self::mul(s, scale);
        }
    }
    fn square_slice(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len());
        for (d, &s) in dst.iter_mut().zip(src) {
            *d = Self::square(s);
        }
    }
}
impl BulkKernels<Gf64> for Reference {
    fn insert_nonzero(odd: &mut [u64], ids: &[u64]) {
        for &id in ids {
            assert_ne!(id, 0);
            let square = Self::square(id);
            let mut power = id;
            for word in odd.iter_mut() {
                *word ^= power;
                power = Self::mul(power, square);
            }
        }
    }
    fn xor_assign(dst: &mut [u64], src: &[u64]) {
        assert_eq!(dst.len(), src.len());
        for (d, &s) in dst.iter_mut().zip(src) {
            *d ^= s;
        }
    }
    fn horner_many(coefficients: &[u64], points: &[u64], out: &mut [u64]) {
        assert_eq!(points.len(), out.len());
        for (&point, value) in points.iter().zip(out) {
            *value = coefficients
                .iter()
                .rev()
                .fold(0, |v, &c| Self::mul(v, point) ^ c);
        }
    }
}

struct SingletonDecoder<const ALTERNATE_ROOTS: bool>;
struct SingletonExecution<const ALTERNATE_ROOTS: bool> {
    budget: RowBudget,
    step: usize,
    failure: Option<DecodeFailure>,
}
const STAGES: [Stage; 7] = [
    Stage::Reconstruction,
    Stage::BerlekampMassey,
    Stage::CandidateEvaluation,
    Stage::Deflation,
    Stage::Leaf,
    Stage::Verification,
    Stage::Canonicalization,
];

impl<const ALTERNATE_ROOTS: bool> RowDecoder<Gf64, Reference>
    for SingletonDecoder<ALTERNATE_ROOTS>
{
    type Execution = SingletonExecution<ALTERNATE_ROOTS>;
    fn begin(budget: RowBudget) -> Self::Execution {
        SingletonExecution {
            budget,
            step: 0,
            failure: None,
        }
    }
}
impl<const ALTERNATE_ROOTS: bool> RowExecution for SingletonExecution<ALTERNATE_ROOTS> {
    fn next_stage(&self) -> Option<Stage> {
        if self.failure.is_some() {
            None
        } else {
            STAGES.get(self.step).copied()
        }
    }
    fn run_next(
        &mut self,
        input: RowInput<'_>,
        workspace: &mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowProgress, DecodeError> {
        let stage = self.next_stage().expect("unfinished singleton row");
        let capacity = input.difference.len();
        let charge = match stage {
            Stage::Reconstruction => Charge::Reconstruct { capacity },
            Stage::BerlekampMassey => Charge::BmStep {
                budget: self.budget.nonzero,
            },
            Stage::CandidateEvaluation => Charge::Candidates {
                degree: 1,
                inputs: input.candidates.len(),
            },
            Stage::Deflation => Charge::Deflate { degree: 1 },
            Stage::Leaf => Charge::Leaf { degree: 1 },
            Stage::Verification => Charge::Verify {
                capacity,
                output_budget: self.budget.total,
            },
            Stage::Canonicalization => Charge::Canonicalize {
                ids: self.budget.total,
            },
            _ => unreachable!("singleton rows do not split"),
        };
        for _ in 0..if stage == Stage::BerlekampMassey {
            2 * capacity
        } else {
            1
        } {
            meter.charge(WorkScheduleV1::cost(charge)?)?;
        }
        match stage {
            Stage::BerlekampMassey if self.budget.nonzero == 0 => {
                self.failure = Some(DecodeFailure::DegreeExceedsBudget);
            }
            Stage::Leaf => workspace.roots[0] = input.difference[0],
            Stage::Verification => {
                workspace.verification.fill(0);
                Reference::insert_nonzero(workspace.verification, &workspace.roots[..1]);
                if workspace.verification != input.difference {
                    self.failure = Some(DecodeFailure::VerificationFailed);
                }
            }
            _ => {}
        }
        self.step += 1;
        Ok(RowProgress {
            stage,
            locator_degree: 1,
            candidate_hits: 0,
            trace_attempts: 0,
            gcd_degree: 0,
        })
    }
    fn finish<'w>(
        mut self,
        input: RowInput<'_>,
        workspace: &'w mut RowWorkspace<'_>,
        meter: &mut WorkMeter,
    ) -> Result<RowResult<'w>, DecodeError> {
        while self.next_stage().is_some() {
            self.run_next(input, workspace, meter)?;
        }
        if let Some(reason) = self.failure {
            return Ok(RowResult::Failed(reason));
        }
        if ALTERNATE_ROOTS {
            workspace.bm[0] = workspace.roots[0];
            workspace.roots[0] = 2;
            Ok(RowResult::Decoded(&workspace.bm[..1]))
        } else {
            Ok(RowResult::Decoded(&workspace.roots[..1]))
        }
    }
}

// Both paths cross the same admitted request/publication and row-driver interfaces.
// Only the staged path advances rows before calling the consuming, draining finish.
fn compose<'s, const ALTERNATE_ROOTS: bool>(
    request: DecodeRequest<'_, Gf64>,
    arena: &'s mut DecodeScratch<Gf64>,
    staged: bool,
) -> Result<DecodeReport<'s>, DecodeError> {
    let mut admitted = admit(&request, arena)?;
    let (mut workspace, results) = arena.split(&admitted.layout);
    let mut publication = Publication::new(results, &admitted.layout);
    admitted
        .meter
        .charge(WorkScheduleV1::cost(Charge::Normalize {
            inputs: request.candidates.len(),
        })?)?;
    assert!(request.candidates.is_empty(), "this fixture has no hints");
    let mut local_offset = 0;
    for (bucket, &capacity) in request.local.shape().capacities().iter().enumerate() {
        let c = usize::from(capacity);
        let zero = bucket == 0
            && (request.local.state.zero_words[0] & 1 != 0) != request.remote.zero(0).unwrap();
        let total = request.limits.max_output_per_bucket;
        let nonzero = total.checked_sub(usize::from(zero)).unwrap();
        admitted
            .meter
            .charge(WorkScheduleV1::cost(Charge::Compare { capacity: c })?)?;
        let row = RowLayout::new(c, nonzero)?;
        let (preprocessing, difference, mut row_workspace) = workspace.row(&row);
        for (index, word) in difference.iter_mut().enumerate() {
            *word = request.local.state.words[local_offset + index]
                ^ request.remote.odd_syndrome(bucket, index).unwrap();
        }
        local_offset += c;
        if !zero && difference.iter().all(|&word| word == 0) {
            publication.write(bucket, DecodeOutcome::Equal, false);
            continue;
        }
        let input = RowInput {
            difference,
            candidates: &preprocessing[..0],
        };
        let mut execution =
            SingletonDecoder::<ALTERNATE_ROOTS>::begin(RowBudget { nonzero, total });
        if staged {
            while execution.next_stage().is_some() {
                let progress =
                    execution.run_next(input, &mut row_workspace, &mut admitted.meter)?;
                assert_eq!(progress.stage, STAGES[execution.step - 1]);
            }
        }
        let result = execution.finish(input, &mut row_workspace, &mut admitted.meter)?;
        match result {
            RowResult::Equal => publication.write(bucket, DecodeOutcome::Equal, false),
            RowResult::Failed(reason) => {
                publication.write(bucket, DecodeOutcome::Failed { reason }, false);
            }
            RowResult::Decoded(roots) => {
                publication.write(bucket, DecodeOutcome::Decoded { ids: roots }, zero);
            }
        }
    }
    publication.finish(admitted.meter.used(), admitted.layout.total_bytes())
}

fn singleton_record(capacities: &[u16], roots: &[u64], zero: bool) -> Vec<u8> {
    let mut bytes = record(capacities, zero);
    let mut offset = 24 + 2 * capacities.len() + capacities.len().div_ceil(8);
    for (&capacity, &root) in capacities.iter().zip(roots) {
        let mut odd = vec![0; usize::from(capacity)];
        if root != 0 {
            Reference::insert_nonzero(&mut odd, &[root]);
        }
        for word in odd {
            bytes[offset..offset + 8].copy_from_slice(&word.to_le_bytes());
            offset += 8;
        }
    }
    bytes
}

#[test]
fn rows_compose_on_one_arena() {
    let capacities = [2, 1, 2, 1];
    let local_bytes = record(&capacities, false);
    let remote_bytes = singleton_record(&capacities, &[4, 0, 2, 0], false);
    let local = owned(&local_bytes);
    let remote = SketchView::parse(&remote_bytes, &wire_limits()).unwrap();
    let plan = DecodePlan::v1();
    let caps = limits(1);
    let layout = ScratchLayout::for_plan(&plan, &capacities, &[Some(1); 4], 1, 0).unwrap();
    let mut arena = DecodeScratch::new(&layout).unwrap();
    let allocation = arena.words.as_ptr();
    for staged in [true, false] {
        let report = compose::<false>(
            DecodeRequest {
                local: &local,
                remote,
                candidates: &[],
                plan: &plan,
                limits: &caps,
            },
            &mut arena,
            staged,
        )
        .unwrap();
        assert_eq!(
            (0..4)
                .map(|b| report.outcome(b).unwrap())
                .collect::<Vec<_>>(),
            [
                DecodeOutcome::Decoded { ids: &[4] },
                DecodeOutcome::Equal,
                DecodeOutcome::Decoded { ids: &[2] },
                DecodeOutcome::Equal
            ],
            "workspace roots survive later rows and publish in bucket order"
        );
        assert_eq!(
            report.result_offsets(),
            [(0, 1), (0, 0), (1, 1), (0, 0)],
            "packed result offsets"
        );
        assert_eq!(
            report.work,
            WorkUnits(1183),
            "one meter across both rows and equal comparisons"
        );
        assert_eq!(report.peak_scratch_bytes, layout.total_bytes());
    }
    assert_eq!(
        arena.words.as_ptr(),
        allocation,
        "maximum-row workspace is reused"
    );
}

fn check_verification_boundary(
    request: DecodeRequest<'_, Gf64>,
    arena: &mut DecodeScratch<Gf64>,
    prefix: u64,
    verify: u64,
) {
    let mut admitted = admit(&request, arena).unwrap();
    let (mut workspace, _) = arena.split(&admitted.layout);
    let total = request.limits.max_output_per_bucket;
    let nonzero = total - usize::from(request.remote.zero(0).unwrap());
    let capacity = request.local.shape().capacities()[0];
    for charge in [
        Charge::Normalize { inputs: 0 },
        Charge::Compare {
            capacity: usize::from(capacity),
        },
    ] {
        admitted
            .meter
            .charge(WorkScheduleV1::cost(charge).unwrap())
            .unwrap();
    }
    let row = RowLayout::new(usize::from(capacity), nonzero).unwrap();
    let (_, difference, mut row_workspace) = workspace.row(&row);
    for (index, word) in difference.iter_mut().enumerate() {
        *word = request.local.state.words[index] ^ request.remote.odd_syndrome(0, index).unwrap();
    }
    let input = RowInput {
        difference,
        candidates: &[],
    };
    let mut execution = SingletonDecoder::<false>::begin(RowBudget { nonzero, total });
    while execution.next_stage() != Some(Stage::Verification) {
        execution
            .run_next(input, &mut row_workspace, &mut admitted.meter)
            .unwrap();
    }
    assert_eq!(
        admitted.meter.used(),
        WorkUnits(prefix),
        "exact work before verification"
    );
    let result = execution.run_next(input, &mut row_workspace, &mut admitted.meter);
    if request.limits.max_work < WorkUnits(prefix + verify) {
        assert_eq!(
            result.map(|progress| progress.stage),
            Err(DecodeError::WorkLimitExceeded),
            "verification must not execute below its total-beta charge; beta={total}"
        );
        assert_eq!(
            admitted.meter.used(),
            WorkUnits(prefix),
            "failed charge performs no verification work"
        );
    } else {
        assert_eq!(
            result.unwrap().stage,
            Stage::Verification,
            "exact verification allowance runs verification"
        );
        assert_eq!(
            admitted.meter.used(),
            WorkUnits(prefix + verify),
            "verification charges the golden total-beta amount"
        );
        assert_eq!(execution.next_stage(), Some(Stage::Canonicalization));
    }
}

#[test]
fn zero_budget_verification_limits_match_paths() {
    let local_bytes = record(&[2], false);
    let local = owned(&local_bytes);
    let plan = DecodePlan::v1();
    // Prefix 576 = admission 2 + compare 3 + reconstruct 6 + BM 560 + deflate 4 + leaf 1.
    for vector in include_str!("../../../tests/vectors/work-zero-v1.tsv")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
    {
        let fields: Vec<u64> = vector
            .split_whitespace()
            .map(|word| word.parse().unwrap())
            .collect();
        let [zero, beta, nonzero, prefix, verify, canonicalize] = fields[..] else {
            panic!("invalid zero-work vector")
        };
        assert_eq!(
            (nonzero, prefix),
            (1, 576),
            "same lower row inputs before total-beta charges"
        );
        let zero = zero != 0;
        let beta = usize::try_from(beta).unwrap();
        let remote_bytes = singleton_record(&[2], &[1], zero);
        let remote = SketchView::parse(&remote_bytes, &wire_limits()).unwrap();
        let layout = ScratchLayout::for_plan(&plan, &[2], &[Some(1)], beta, 0).unwrap();
        let mut arena = DecodeScratch::new(&layout).unwrap();
        for allowance in [verify - 1, verify, verify + canonicalize] {
            let mut caps = limits(beta);
            caps.max_work = WorkUnits(prefix + allowance);
            check_verification_boundary(
                DecodeRequest {
                    local: &local,
                    remote,
                    candidates: &[],
                    plan: &plan,
                    limits: &caps,
                },
                &mut arena,
                prefix,
                verify,
            );
            for staged in [true, false] {
                let result = compose::<false>(
                    DecodeRequest {
                        local: &local,
                        remote,
                        candidates: &[],
                        plan: &plan,
                        limits: &caps,
                    },
                    &mut arena,
                    staged,
                );
                if allowance < verify + canonicalize {
                    assert_eq!(
                        result.map(|_| ()),
                        Err(DecodeError::WorkLimitExceeded),
                        "verification/canonicalization use total beta, including zero; \
                         beta={beta} allowance={allowance} staged={staged}"
                    );
                } else {
                    let report = result.unwrap();
                    let expected: &[u64] = if zero { &[0, 1] } else { &[1] };
                    assert_eq!(
                        report.outcome(0),
                        Some(DecodeOutcome::Decoded { ids: expected })
                    );
                    assert_eq!(
                        report.work,
                        WorkUnits(prefix + verify + canonicalize),
                        "exact V1 total-beta work"
                    );
                }
            }
        }
    }
}

#[test]
fn zero_publication_uses_returned_roots() {
    let local_bytes = record(&[2], false);
    let remote_bytes = singleton_record(&[2], &[1], true);
    let local = owned(&local_bytes);
    let remote = SketchView::parse(&remote_bytes, &wire_limits()).unwrap();
    let plan = DecodePlan::v1();
    let caps = limits(2);
    let layout = ScratchLayout::for_plan(&plan, &[2], &[Some(1)], 2, 0).unwrap();
    let mut arena = DecodeScratch::new(&layout).unwrap();
    for staged in [true, false] {
        let report = compose::<true>(
            DecodeRequest {
                local: &local,
                remote,
                candidates: &[],
                plan: &plan,
                limits: &caps,
            },
            &mut arena,
            staged,
        )
        .unwrap();
        assert_eq!(
            report.outcome(0),
            Some(DecodeOutcome::Decoded { ids: &[0, 1] }),
            "zero publication must copy the returned verified slice, not stale roots"
        );
        assert_eq!(report.result_offsets(), [(0, 2)]);
    }
}
