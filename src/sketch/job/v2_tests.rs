#![forbid(unsafe_code)]

use {
    super::*,
    crate::{
        BackendRequest, DecodeError, DecodeLimits, DecodePlan, Decoder, FrozenSketch, Gf64,
        MutableSketch, ParseLimits, ScratchLayout, ShapeLimits, SketchShape, SketchView, WorkUnits,
    },
    std::sync::Arc,
};

// Keep fault injection and observations on the selected production execution.
macro_rules! with_row {
    ($execution:expr, $row:ident, $body:expr) => {
        match $execution {
            DecodeExecution::Probe($row, _) => $body,
            DecodeExecution::Portable($row) => $body,
            #[cfg(target_arch = "x86_64")]
            DecodeExecution::Pclmul($row) => $body,
            #[cfg(target_arch = "x86_64")]
            DecodeExecution::Vpclmul512($row) => $body,
        }
    };
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Equal,
    Decoded(Vec<u64>),
    Failed(DecodeFailure),
}

#[derive(Debug, PartialEq, Eq)]
struct Observed {
    rows: Vec<Outcome>,
    stages: Vec<Stage>,
    work: u64,
    algebra: Vec<(u64, u64, u64)>,
}

struct Fixture {
    local: FrozenSketch<Gf64>,
    remote: Vec<u8>,
    zero: bool,
}

impl Fixture {
    fn new(rows: &[&[u64]], zero: bool) -> Self {
        let capacities: Vec<_> = rows.iter().map(|row| row.len()).collect();
        let shape = Arc::new(
            SketchShape::new(
                &capacities,
                &ShapeLimits {
                    max_wire_bytes: 100_000,
                    max_buckets: 16,
                    max_capacity_per_bucket: 89,
                    max_total_syndrome_words: 1424,
                },
            )
            .unwrap(),
        );
        let local = MutableSketch::new(shape, BackendRequest::Auto)
            .unwrap()
            .freeze();
        let mut remote = local.encoded_v1().unwrap().to_vec();
        let flags = 24 + 2 * rows.len();
        remote[flags] = u8::from(zero);
        let start = flags + rows.len().div_ceil(8);
        for (bytes, word) in remote[start..]
            .chunks_exact_mut(8)
            .zip(rows.iter().flat_map(|r| r.iter()))
        {
            bytes.copy_from_slice(&word.to_le_bytes());
        }
        Self {
            local,
            remote,
            zero,
        }
    }

    fn view(&self) -> SketchView<'_, Gf64> {
        SketchView::parse(
            &self.remote,
            &ParseLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap()
    }

    fn layout(&self, plan: DecodePlan, beta: usize, hints: usize) -> (WorkUnits, ScratchLayout) {
        let budgets: Vec<_> = (0..self.local.shape().bucket_count())
            .map(|b| beta.checked_sub(usize::from(b == 0 && self.zero)))
            .collect();
        plan.complete_bound(self.local.shape().capacities(), &budgets, beta, hints)
            .unwrap()
    }

    fn run(&self, plan: DecodePlan, beta: usize, hints: &[u64], seed: u64) -> Observed {
        self.run_fault(plan, beta, hints, seed, crate::decode::direct::Fault::None)
    }

    fn run_fault(
        &self,
        plan: DecodePlan,
        beta: usize,
        hints: &[u64],
        seed: u64,
        fault: crate::decode::direct::Fault,
    ) -> Observed {
        self.run_backend(plan, beta, hints, seed, fault, BackendRequest::Auto)
    }

    fn run_backend(
        &self,
        plan: DecodePlan,
        beta: usize,
        hints: &[u64],
        seed: u64,
        fault: crate::decode::direct::Fault,
        backend: BackendRequest,
    ) -> Observed {
        let (bound, layout) = self.layout(plan, beta, hints.len());
        let limits = DecodeLimits {
            max_output_per_bucket: beta,
            max_candidate_inputs: hints.len(),
            max_work: bound,
            max_scratch_bytes: layout.total_bytes(),
        };
        let decoder = Decoder::new(backend, seed).unwrap();
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        poison(&mut scratch, 0xdead_beef_1234_5678);
        let request = DecodeRequest {
            local: &self.local,
            remote: self.view(),
            candidates: hints,
            plan: &plan,
            limits: &limits,
        };
        let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
        if let JobState::Row { execution, .. } = &mut job.state {
            with_row!(execution, row, { row.probe_fault = fault });
        }
        for bucket in 0..self.local.shape().bucket_count() {
            let expected: std::collections::BTreeSet<_> = hints
                .iter()
                .copied()
                .filter(|&id| id != 0 && self.local.shape().bucket_for(id) == bucket)
                .collect();
            assert_eq!(
                candidates::row(job.workspace.preprocessing, hints.len(), bucket),
                expected.into_iter().collect::<Vec<_>>(),
                "normalized candidate contents"
            );
        }
        let mut stages = Vec::new();
        let mut algebra = Vec::new();
        while job.next_stage().is_some() {
            match job.run_next() {
                StageProgress::Completed {
                    stage,
                    locator_degree,
                    candidate_hits,
                    trace_attempts,
                    gcd_degree,
                    ..
                } => {
                    if stage == Stage::DirectTwo
                        && let JobState::Row { execution, .. } = &job.state
                        && let Some(values) = with_row!(execution, row, row.probe_algebra)
                    {
                        algebra.push(values);
                    }
                    if stage != Stage::BerlekampMassey && !stages.contains(&Stage::BerlekampMassey)
                    {
                        assert_eq!(
                            (locator_degree, candidate_hits, trace_attempts, gcd_degree),
                            (0, 0, 0, 0),
                            "probes do not run general work"
                        );
                    }
                    stages.push(stage);
                }
                progress @ StageProgress::Failed(_) => panic!("complete bound: {progress:?}"),
            }
        }
        let report = job.finish().unwrap();
        let rows = outcomes(&report);
        let work = report.work.0;
        if matches!(fault, crate::decode::direct::Fault::None) {
            let ordinary = decode_into(request, &decoder, &mut scratch).unwrap();
            let ordinary_rows = outcomes(&ordinary);
            assert_eq!(ordinary_rows, rows, "decode_into and staged publication");
            assert_eq!(
                ordinary.work.0, work,
                "same work through both public entries"
            );
        }
        Observed {
            rows,
            stages,
            work,
            algebra,
        }
    }
}

fn outcomes(report: &DecodeReport<'_>) -> Vec<Outcome> {
    (0..report.bucket_count())
        .map(|b| match report.outcome(b).unwrap() {
            DecodeOutcome::Equal => Outcome::Equal,
            DecodeOutcome::Decoded { ids } => Outcome::Decoded(ids.to_vec()),
            DecodeOutcome::Failed { reason } => Outcome::Failed(reason),
        })
        .collect()
}

fn poison(scratch: &mut DecodeScratch<Gf64>, garbage: u64) {
    scratch.words.fill(garbage);
    scratch.ids.fill(garbage);
    for raw in &mut scratch.raw {
        raw.lo = garbage;
        raw.hi = !garbage;
    }
    for frame in &mut scratch.factors {
        frame.coefficient_start = garbage;
        frame.coefficient_len = garbage;
        frame.next_direction = u32::MAX;
        frame.split_checked = u32::MAX;
    }
}

#[test]
fn v2_stage_order() {
    success(&[3], 1, false, &[3], ONE, 13);
    let top = 1_u64 << 63;
    success(&odd_words(&[top], 3), 3, false, &[top], ONE, 47);

    let fixture = Fixture::new(&[&[1]], false);
    let actual = fixture.run(DecodePlan::v2(), 1, &[], 1);
    assert_eq!(actual.rows, [Outcome::Decoded(vec![1])]);
    assert_eq!(
        actual.stages,
        [
            Stage::DirectOne,
            Stage::Verification,
            Stage::Canonicalization
        ],
        "singleton must complete directly"
    );
    assert_eq!(actual.work, 13, "singleton exact work");
    for line in include_str!("../../../tests/vectors/outcome-v2.tsv")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
    {
        let fields: Vec<_> = line.split_whitespace().collect();
        let words: Vec<_> = fields[4]
            .split(',')
            .map(|word| {
                if let Some(hex) = word.strip_prefix("0x") {
                    u64::from_str_radix(hex, 16).unwrap()
                } else {
                    word.parse().unwrap()
                }
            })
            .collect();
        assert_eq!(words.len(), fields[1].parse::<usize>().unwrap());
        let actual = Fixture::new(&[&words], fields[3] == "1").run(
            DecodePlan::v2(),
            fields[2].parse().unwrap(),
            &[],
            1,
        );
        let expected = match fields[5] {
            "Equal" => Outcome::Equal,
            "DegreeExceedsBudget" => Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
            "NotSplit" => Outcome::Failed(DecodeFailure::NotSplit),
            ids => Outcome::Decoded(ids.split(',').map(|id| id.parse().unwrap()).collect()),
        };
        assert_eq!(actual.rows, [expected], "golden {}", fields[0]);
        assert_eq!(
            actual.work,
            fields[6].parse::<u64>().unwrap(),
            "golden work {}",
            fields[0]
        );
    }
}

#[test]
fn v2_two_algebra() {
    let fixture = Fixture::new(&[&[3, 9]], false);
    let actual = fixture.run(DecodePlan::v2(), 2, &[], 1);
    assert_eq!(actual.rows, [Outcome::Decoded(vec![1, 2])]);
    assert_eq!(
        actual.stages,
        [
            Stage::DirectOne,
            Stage::Verification,
            Stage::DirectTwo,
            Stage::Verification,
            Stage::Canonicalization
        ],
        "pair must complete directly; observed work={}",
        actual.work
    );
    assert_eq!(actual.work, 212, "pair exact work");
    for roots in [[1, 3], [5, 0x100], [1_u64 << 63, u64::MAX]] {
        let words = odd_words(&roots, 2);
        success(&words, 2, false, &roots, TWO, 212);
        let words = odd_words(&roots, 3);
        success(&words, 2, false, &roots, TWO, 227);
    }

    assert_eq!(
        actual.algebra,
        [(2, 0xaaaa_aaaa_aaaa_aaa4, 0xffff_ffff_ffff_fff6)],
        "fixed free coordinate in the actual probe"
    );
}

#[test]
fn v2_complete_bounds() {
    let plan = DecodePlan { version: 2 };
    for (c, r, beta, v1, v2) in [
        (1, 1, 1, 459, 467),
        (2, 2, 2, 948, 1151),
        (3, 2, 3, 1263, 1494),
        (3, 2, 2, 1251, 1468),
        (2, 1, 1, 748, 761),
    ] {
        let expected = DecodePlan::v1()
            .complete_bound(&[c], &[Some(r)], beta, 0)
            .unwrap();
        assert_eq!(expected.0, WorkUnits(v1));
        let actual = plan.complete_bound(&[c], &[Some(r)], beta, 0);
        assert_eq!(
            actual,
            Ok((WorkUnits(v2), expected.1)),
            "selected V2 complete bound"
        );
    }
    success(&[1], 1, false, &[1], ONE, 13);
    success(&[3, 9], 2, false, &[1, 2], TWO, 212);
    for (name, charge) in [
        ("DirectOne", crate::decode::work::Charge::DirectOne),
        ("DirectTwo", crate::decode::work::Charge::DirectTwo),
    ] {
        let line = include_str!("../../../tests/vectors/work-v2.tsv")
            .lines()
            .find(|line| line.starts_with(name))
            .unwrap();
        let units: u64 = line.split_whitespace().nth(3).unwrap().parse().unwrap();
        assert_eq!(
            crate::decode::work::WorkScheduleV1::cost(charge).unwrap(),
            WorkUnits(units)
        );
    }
    assert_eq!(
        plan.complete_bound(&[65535; 16], &[Some(65535); 16], 65535, 0),
        Err(DecodeError::WorkLimitExceeded)
    );
    assert_eq!(
        plan.complete_bound(&[1], &[Some(0)], 0, usize::MAX),
        Err(DecodeError::WorkLimitExceeded),
        "work overflow before layout"
    );
}

const ONE: &[Stage] = &[
    Stage::DirectOne,
    Stage::Verification,
    Stage::Canonicalization,
];
const TWO: &[Stage] = &[
    Stage::DirectOne,
    Stage::Verification,
    Stage::DirectTwo,
    Stage::Verification,
    Stage::Canonicalization,
];
const DEGREE: &[Stage] = &[Stage::Reconstruction, Stage::BerlekampMassey];
const GENERAL: &[Stage] = &[
    Stage::Reconstruction,
    Stage::BerlekampMassey,
    Stage::CandidateEvaluation,
    Stage::Deflation,
    Stage::Leaf,
    Stage::Verification,
    Stage::Canonicalization,
];

fn success(words: &[u64], beta: usize, zero: bool, ids: &[u64], stages: &[Stage], work: u64) {
    let actual = Fixture::new(&[words], zero).run(DecodePlan::v2(), beta, &[], 1);
    assert_eq!(actual.rows, [Outcome::Decoded(ids.to_vec())]);
    assert_eq!(
        actual.stages, stages,
        "direct success cannot hide behind fallback"
    );
    assert_eq!(actual.work, work, "frozen direct work");
}

fn fallback(
    words: &[u64],
    beta: usize,
    probes: &[Stage],
    general: &[Stage],
    extra: u64,
    total: u64,
) {
    let fixture = Fixture::new(&[words], false);
    let v1 = fixture.run(DecodePlan::v1(), beta, &[], 1);
    assert_eq!(v1.stages, general, "frozen V1 suffix");
    assert_eq!(v1.work, total - extra, "frozen V1 work");
    let v2 = fixture.run(DecodePlan::v2(), beta, &[], 1);
    assert_eq!(v2.rows, v1.rows, "miss preserves IDs, class and reason");
    assert_eq!(
        v2.stages,
        [probes, general].concat(),
        "exact miss prefix and V1 suffix"
    );
    assert_eq!(v2.work, total, "frozen fallback ledger");
}

#[test]
fn v2_one_checks_last_syndrome() {
    success(&[1, 1, 1], 3, false, &[1], ONE, 47);
    fallback(
        &[1, 1, 0],
        3,
        &[Stage::DirectOne, Stage::Verification, Stage::DirectTwo],
        DEGREE,
        200,
        975,
    );
}

#[test]
fn v2_two_checks_last_syndrome() {
    success(&[3, 9, 33], 2, false, &[1, 2], TWO, 227);
    fallback(&[3, 9, 32], 2, &TWO[..4], DEGREE, 217, 962);
}

#[test]
fn v2_guards_and_zero_budget() {
    check_ineligible_stages();
    success(&[1], 1, false, &[1], ONE, 13);
    success(&[1, 1], 2, true, &[0, 1], ONE, 27);
    success(&[3, 9, 33], 3, true, &[0, 1, 2], TWO, 246);
    let plan = DecodePlan::v2();
    for (words, zero, beta, outcome, stages, work) in [
        (
            &[0][..],
            true,
            0,
            Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
            &[][..],
            2,
        ),
        (&[0][..], false, 1, Outcome::Equal, &[][..], 4),
        (&[0][..], true, 1, Outcome::Decoded(vec![0]), GENERAL, 283),
        (
            &[1][..],
            false,
            0,
            Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
            DEGREE,
            141,
        ),
        (
            &[3, 9][..],
            false,
            1,
            Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
            &[
                Stage::DirectOne,
                Stage::Verification,
                Stage::Reconstruction,
                Stage::BerlekampMassey,
            ][..],
            444,
        ),
    ] {
        let actual = Fixture::new(&[words], zero).run(plan, beta, &[], 1);
        assert_eq!(actual.rows, [outcome]);
        assert_eq!(actual.stages, stages, "eligibility and zero handling");
        assert_eq!(actual.work, work);
    }
}

#[test]
fn v2_s1_zero_falls_back() {
    fallback(&[0, 1], 2, &[], DEGREE, 0, 449);
    let fixture = Fixture::new(&[&[0, 6, 18]], false);
    let v1 = fixture.run(DecodePlan::v1(), 3, &[], 1);
    let v2 = fixture.run(DecodePlan::v2(), 3, &[], 1);
    let mut stages = vec![
        Stage::Reconstruction,
        Stage::BerlekampMassey,
        Stage::CandidateEvaluation,
        Stage::Deflation,
        Stage::ReducerPreparation,
    ];
    for _ in 0..61 {
        stages.extend([Stage::Trace, Stage::Gcd]);
    }
    stages.extend([
        Stage::FactorDivision,
        Stage::Leaf,
        Stage::Leaf,
        Stage::Verification,
        Stage::Canonicalization,
    ]);
    assert_eq!(v1.stages, stages, "frozen valid S1-zero general trace");
    assert_eq!(v1.work, 175_020, "independent V1 charge ledger");
    assert_eq!(v1.rows, [Outcome::Decoded(vec![1, 2, 3])]);
    assert_eq!(v2, v1, "S1 zero must not imply equality or a probe failure");
}

#[test]
fn v2_degenerate_quadratics() {
    success(&[3, 9], 2, false, &[1, 2], TWO, 212);
    fallback(
        &[1, 1, 0],
        3,
        &[Stage::DirectOne, Stage::Verification, Stage::DirectTwo],
        DEGREE,
        200,
        975,
    );
    fallback(
        &[1, 0x2000_0000_0000_0001],
        2,
        &[Stage::DirectOne, Stage::Verification, Stage::DirectTwo],
        &GENERAL[..5],
        186,
        953,
    );
    let fixture = Fixture::new(&[&[3, 9, 32]], false);
    let v1 = fixture.run(DecodePlan::v1(), 2, &[], 1);
    for fault in [
        crate::decode::direct::Fault::BadMap,
        crate::decode::direct::Fault::EqualRoots,
        crate::decode::direct::Fault::ZeroRoot,
    ] {
        let actual = fixture.run_fault(DecodePlan::v2(), 2, &[], 1, fault);
        assert_eq!(
            actual.rows, v1.rows,
            "ordinary fallback after injected provisional arithmetic fault {fault:?}"
        );
        assert_eq!(
            actual.stages,
            [
                Stage::DirectOne,
                Stage::Verification,
                Stage::DirectTwo,
                Stage::Reconstruction,
                Stage::BerlekampMassey
            ],
            "reject before entering pair verification: {fault:?}"
        );
        assert_eq!(
            actual.work, 938,
            "no verification charge for invalid algebraic pair: {fault:?}"
        );
    }
}

#[test]
fn v2_mapping_before_acceptance() {
    success(&[1], 1, false, &[1], ONE, 13);
    let fixture = Fixture::new(&[&[1], &[0]], false);
    let v1 = fixture.run(DecodePlan::v1(), 1, &[], 1);
    let v2 = fixture.run(DecodePlan::v2(), 1, &[], 1);
    assert_eq!(
        v1.rows,
        [
            Outcome::Failed(DecodeFailure::InvalidLocator),
            Outcome::Equal
        ]
    );
    assert_eq!(v1.stages, GENERAL);
    assert_eq!(v1.work, 303);
    assert_eq!(v2.rows, v1.rows);
    assert_eq!(
        v2.stages,
        [&ONE[..2], GENERAL].concat(),
        "upper rejection resumes general decoding"
    );
    assert_eq!(v2.work, 311);
}

#[test]
fn v2_candidates_do_not_authorize() {
    let fixture = Fixture::new(&[&[3, 9]], false);
    for (hints, work) in [
        (&[][..], 212),
        (&[1][..], 215),
        (&[1, 2][..], 220),
        (&[4, 5][..], 220),
        (&[1, 1, 0][..], 227),
    ] {
        let actual = fixture.run(DecodePlan::v2(), 2, hints, 1);
        assert_eq!(actual.rows, [Outcome::Decoded(vec![1, 2])]);
        assert_eq!(actual.stages, TWO, "hints never bypass probes");
        assert_eq!(actual.work, work, "raw normalization charge");
    }
    for words in [&[1, 1, 0][..], &[3, 9, 32][..]] {
        let fixture = Fixture::new(&[words], false);
        for hints in [&[][..], &[1, 2][..], &[0, 1, 1, 2, 5][..]] {
            let v1 = fixture.run(DecodePlan::v1(), 2, hints, 1);
            assert_eq!(fixture.run(DecodePlan::v2(), 2, hints, 1).rows, v1.rows);
        }
    }
}

fn snapshot(workspace: &mut DecodeWorkspace<'_>, layout: &RowLayout) -> Vec<u8> {
    let (preprocessing, difference, row) = workspace.row(layout);
    let mut bytes = Vec::new();
    for values in [
        preprocessing,
        difference,
        row.syndromes,
        row.bm,
        row.polynomials,
        row.factors,
        row.square_table,
        row.verification,
        row.roots,
    ] {
        bytes.extend(values.iter().flat_map(|value| value.to_ne_bytes()));
    }
    for raw in row.raw {
        bytes.extend(raw.lo.to_ne_bytes());
        bytes.extend(raw.hi.to_ne_bytes());
    }
    for frame in row.stack {
        bytes.extend(frame.coefficient_start.to_ne_bytes());
        bytes.extend(frame.coefficient_len.to_ne_bytes());
        bytes.extend(frame.next_direction.to_ne_bytes());
        bytes.extend(frame.split_checked.to_ne_bytes());
    }
    bytes
}

#[test]
fn v2_charge_boundaries() {
    success(&[1], 1, false, &[1], ONE, 13);
    success(&[3, 9], 2, false, &[1, 2], TWO, 212);
    for (words, beta, stages, charges, initial) in [
        (&[1][..], 1, ONE, &[1, 7, 1][..], 4),
        (&[3, 9][..], 2, TWO, &[1, 17, 168, 17, 4][..], 5),
        (&[2, 14][..], 2, TWO, &[1, 17, 168, 17, 4][..], 5),
    ] {
        let fixture = Fixture::new(&[words], false);
        let plan = DecodePlan::v2();
        let (_, layout) = fixture.layout(plan, beta, 0);
        let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
        let mut prefix = initial;
        for (boundary, (&stage, &charge)) in stages.iter().zip(charges).enumerate() {
            for cap in [prefix, prefix + charge - 1] {
                let limits = DecodeLimits {
                    max_output_per_bucket: beta,
                    max_candidate_inputs: 0,
                    max_work: WorkUnits(cap),
                    max_scratch_bytes: layout.total_bytes(),
                };
                let request = DecodeRequest {
                    local: &fixture.local,
                    remote: fixture.view(),
                    candidates: &[],
                    plan: &plan,
                    limits: &limits,
                };
                let mut scratch = DecodeScratch::new(&layout).unwrap();
                scratch.words.fill(0xface_beef_1234_5678);
                let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
                let observer = Arc::new(std::sync::atomic::AtomicUsize::new(0));
                if let JobState::Row { execution, .. } = &mut job.state {
                    with_row!(execution, row, {
                        row.operation_observer = Some(Arc::clone(&observer));
                    });
                }
                for &prior in &stages[..boundary] {
                    assert_eq!(job.next_stage(), Some(prior));
                    assert!(matches!(job.run_next(), StageProgress::Completed { .. }));
                }
                assert_eq!(job.next_stage(), Some(stage));
                assert_eq!(job.meter.used(), WorkUnits(prefix));
                let JobState::Row {
                    layout: row_layout, ..
                } = &job.state
                else {
                    panic!("active row")
                };
                let row_layout = row_layout.clone();
                let before = snapshot(&mut job.workspace, &row_layout);
                let operations = observer.load(std::sync::atomic::Ordering::Relaxed);
                assert_eq!(
                    job.run_next(),
                    StageProgress::Failed(DecodeError::WorkLimitExceeded)
                );
                assert_eq!(
                    job.meter.used(),
                    WorkUnits(prefix),
                    "failed charge has no partial payment"
                );
                assert_eq!(
                    observer.load(std::sync::atomic::Ordering::Relaxed),
                    operations,
                    "failed charge executes no operation, including pure algebra"
                );
                assert_eq!(
                    snapshot(&mut job.workspace, &row_layout),
                    before,
                    "charge before {stage:?}, cap={cap}"
                );
                assert_eq!(job.next_stage(), None);
                assert_eq!(
                    job.run_next(),
                    StageProgress::Failed(DecodeError::WorkLimitExceeded)
                );
                assert_eq!(
                    job.finish().map(|_| ()),
                    Err(DecodeError::WorkLimitExceeded)
                );
                assert_eq!(
                    decode_into(request, &decoder, &mut scratch).map(|_| ()),
                    Err(DecodeError::WorkLimitExceeded)
                );
            }
            prefix += charge;
        }
    }
}

#[test]
fn v2_atomic_publication() {
    let fixture = Fixture::new(&[&[2], &[1]], false);
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let (_, layout) = fixture.layout(plan, 1, 0);
    for cap in [24, 25] {
        let limits = DecodeLimits {
            max_output_per_bucket: 1,
            max_candidate_inputs: 0,
            max_work: WorkUnits(cap),
            max_scratch_bytes: layout.total_bytes(),
        };
        let request = DecodeRequest {
            local: &fixture.local,
            remote: fixture.view(),
            candidates: &[],
            plan: &plan,
            limits: &limits,
        };
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
        let mut trace = Vec::new();
        while job.next_stage().is_some() {
            match job.run_next() {
                StageProgress::Completed { bucket, stage, .. } => trace.push((bucket, stage)),
                other @ StageProgress::Failed(_) => {
                    assert_eq!(other, StageProgress::Failed(DecodeError::WorkLimitExceeded));
                }
            }
        }
        assert_eq!(
            &trace[..3],
            &[
                (0, Stage::DirectOne),
                (0, Stage::Verification),
                (0, Stage::Canonicalization)
            ]
        );
        assert_eq!(job.meter.used(), WorkUnits(cap));
        if cap == 24 {
            assert_eq!(trace.len(), 5);
            assert_eq!(
                job.run_next(),
                StageProgress::Failed(DecodeError::WorkLimitExceeded)
            );
            assert_eq!(
                job.finish().map(|_| ()),
                Err(DecodeError::WorkLimitExceeded)
            );
        } else {
            assert_eq!(trace.len(), 6);
            let report = job.finish().unwrap();
            assert_eq!(
                report.outcome(0),
                Some(DecodeOutcome::Decoded { ids: &[2] })
            );
            assert_eq!(
                report.outcome(1),
                Some(DecodeOutcome::Decoded { ids: &[1] })
            );
        }
        {
            let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
            job.run_next();
        }
        assert_eq!(
            decode_into(request, &decoder, &mut scratch).is_ok(),
            cap == 25,
            "drop publishes nothing and arena is reusable"
        );
    }
}

fn check_admission_modes() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    for (words, zero, beta) in [
        (&[1][..], false, 1),
        (&[0][..], false, 1),
        (&[0][..], true, 0),
    ] {
        let fixture = Fixture::new(&[words], zero);
        let (_, layout) = fixture.layout(plan, beta, 1);
        let mut limits = DecodeLimits {
            max_output_per_bucket: beta,
            max_candidate_inputs: 0,
            max_work: WorkUnits(0),
            max_scratch_bytes: 0,
        };
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        scratch.outcomes.clear();
        for expected in [
            DecodeError::CandidateLimitExceeded,
            DecodeError::WorkLimitExceeded,
            DecodeError::ScratchTooSmall,
        ] {
            let request = DecodeRequest {
                local: &fixture.local,
                remote: fixture.view(),
                candidates: &[1],
                plan: &plan,
                limits: &limits,
            };
            assert_eq!(
                DecodeJob::new(request, &decoder, &mut scratch).map(|_| ()),
                Err(expected),
                "admission before tiny/equal/underflow classification"
            );
            assert_eq!(
                decode_into(request, &decoder, &mut scratch).map(|_| ()),
                Err(expected)
            );
            if expected == DecodeError::CandidateLimitExceeded {
                limits.max_candidate_inputs = 1;
            } else {
                limits.max_work = WorkUnits(u64::MAX);
            }
        }
        let bad_plan = DecodePlan { version: 99 };
        let request = DecodeRequest {
            local: &fixture.local,
            remote: fixture.view(),
            candidates: &[1],
            plan: &bad_plan,
            limits: &limits,
        };
        assert_eq!(
            DecodeJob::new(request, &decoder, &mut scratch).map(|_| ()),
            Err(DecodeError::InvalidPlan)
        );
        let mismatch = Fixture::new(&[&[0, 0]], false);
        assert_eq!(
            decode_into(
                DecodeRequest {
                    remote: mismatch.view(),
                    ..request
                },
                &decoder,
                &mut scratch
            )
            .map(|_| ()),
            Err(DecodeError::ShapeMismatch)
        );
    }
    success(&[1], 1, false, &[1], ONE, 13);
    success(&[3, 9], 2, false, &[1, 2], TWO, 212);
}

fn check_parser_and_bound_admission() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let mut malformed = Fixture::new(&[&[0], &[0]], false);
    malformed.remote[28] = 2;
    assert_eq!(
        SketchView::<Gf64>::parse(
            &malformed.remote,
            &ParseLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424
            }
        )
        .unwrap_err(),
        crate::ParseError::InvalidEncoding
    );

    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[65535; 16],
            &ShapeLimits {
                max_wire_bytes: 10_000_000,
                max_buckets: 16,
                max_capacity_per_bucket: 65535,
                max_total_syndrome_words: 1_048_560,
            },
        )
        .unwrap(),
    );
    let local = MutableSketch::new(shape, BackendRequest::Auto)
        .unwrap()
        .freeze();
    let remote = SketchView::parse(
        local.encoded_v1().unwrap(),
        &ParseLimits {
            max_wire_bytes: 10_000_000,
            max_buckets: 16,
            max_capacity_per_bucket: 65535,
            max_total_syndrome_words: 1_048_560,
        },
    )
    .unwrap();
    let limits = DecodeLimits {
        max_output_per_bucket: 65535,
        max_candidate_inputs: 0,
        max_work: WorkUnits(u64::MAX),
        max_scratch_bytes: 0,
    };
    let (_, tiny) = plan.complete_bound(&[1], &[Some(0)], 0, 0).unwrap();
    let mut scratch = DecodeScratch::new(&tiny).unwrap();
    let request = DecodeRequest {
        local: &local,
        remote,
        candidates: &[],
        plan: &plan,
        limits: &limits,
    };
    assert_eq!(
        DecodeJob::new(request, &decoder, &mut scratch).map(|_| ()),
        Err(DecodeError::WorkLimitExceeded),
        "selected complete-bound overflow precedes short scratch on equal input"
    );
    assert_eq!(
        decode_into(request, &decoder, &mut scratch).map(|_| ()),
        Err(DecodeError::WorkLimitExceeded)
    );
}

#[test]
fn v2_admission_precedes_probes() {
    check_raw_candidate_count();
    check_b1_v2_vectors();
    check_admission_modes();
    check_parser_and_bound_admission();
}

#[test]
fn v2_fallback_uses_original_input() {
    let plan = DecodePlan::v2();
    let (_, layout) = plan.complete_bound(&[3], &[Some(3)], 3, 5).unwrap();
    let mut scratch = DecodeScratch::new(&layout).unwrap();
    let addresses = (
        scratch.words.as_ptr(),
        scratch.raw.as_ptr(),
        scratch.factors.as_ptr(),
        scratch.ids.as_ptr(),
    );
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    for garbage in [0, 1, u64::MAX, 0x1234_5678_dead_beef] {
        for (words, beta, expected_work, prefix) in [
            (&[1][..], 1, 13, &[][..]),
            (&[3, 9][..], 2, 212, &[][..]),
            (
                &[1, 1, 0][..],
                3,
                975,
                &[Stage::DirectOne, Stage::Verification, Stage::DirectTwo][..],
            ),
            (&[3, 9, 32][..], 2, 962, &TWO[..4]),
        ] {
            let fixture = Fixture::new(&[words], false);
            let (bound, required) = fixture.layout(plan, beta, 0);
            let limits = DecodeLimits {
                max_output_per_bucket: beta,
                max_candidate_inputs: 0,
                max_work: bound,
                max_scratch_bytes: required.total_bytes(),
            };
            let request = DecodeRequest {
                local: &fixture.local,
                remote: fixture.view(),
                candidates: &[],
                plan: &plan,
                limits: &limits,
            };
            poison(&mut scratch, garbage);
            {
                let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
                job.run_next();
                job.run_next();
            }
            let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
            for &stage in prefix {
                assert_eq!(job.next_stage(), Some(stage));
                assert!(matches!(job.run_next(), StageProgress::Completed { .. }));
            }
            if !prefix.is_empty() {
                assert_eq!(job.next_stage(), Some(Stage::Reconstruction));
                let JobState::Row {
                    execution, layout, ..
                } = &job.state
                else {
                    panic!("active fallback")
                };
                assert_eq!(
                    with_row!(execution, row, row.provisional_count()),
                    0,
                    "discard every provisional probe root"
                );
                let (_, difference, _) = job.workspace.row(layout);
                assert_eq!(difference, words, "immutable original odd input");
            }
            let report = job.finish().unwrap();
            assert_eq!(report.work, WorkUnits(expected_work));
            let actual = match report.outcome(0).unwrap() {
                DecodeOutcome::Decoded { ids } => Outcome::Decoded(ids.to_vec()),
                DecodeOutcome::Failed { reason } => Outcome::Failed(reason),
                DecodeOutcome::Equal => Outcome::Equal,
            };
            let v1 = fixture.run(DecodePlan::v1(), beta, &[], 1);
            assert_eq!(actual, v1.rows[0]);
            if prefix.is_empty() {
                let control = fixture.run(plan, beta, &[], 1);
                assert_eq!(control.stages, if beta == 1 { ONE } else { TWO });
                assert_eq!(control.work, expected_work);
            }
        }
    }
    assert_eq!(
        (
            scratch.words.as_ptr(),
            scratch.raw.as_ptr(),
            scratch.factors.as_ptr(),
            scratch.ids.as_ptr()
        ),
        addresses
    );
}

mod corpus;

fn check_ineligible_stages() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    for (words, beta, prefix) in [(&[1][..], 0, &[][..]), (&[3, 9][..], 1, &ONE[..2])] {
        let fixture = Fixture::new(&[words], false);
        let (max_work, layout) = fixture.layout(plan, beta, 0);
        let limits = DecodeLimits {
            max_output_per_bucket: beta,
            max_candidate_inputs: 0,
            max_work,
            max_scratch_bytes: layout.total_bytes(),
        };
        let request = DecodeRequest {
            local: &fixture.local,
            remote: fixture.view(),
            candidates: &[],
            plan: &plan,
            limits: &limits,
        };
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
        for &stage in prefix {
            assert_eq!(job.next_stage(), Some(stage));
            job.run_next();
        }
        assert_eq!(
            job.next_stage(),
            Some(Stage::Reconstruction),
            "ineligible probe cannot touch root storage or absent S3"
        );
    }
}

fn check_b1_v2_vectors() {
    let plan = DecodePlan::v2();
    let fixture = Fixture::new(&[&[0], &[0]], true);
    let (max_work, layout) = fixture.layout(plan, 0, 1);
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    for line in include_str!("../../../tests/vectors/failure-v2.tsv")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
    {
        let fields: Vec<_> = line.split_whitespace().collect();
        let limits = DecodeLimits {
            max_output_per_bucket: 0,
            max_candidate_inputs: fields[1].parse().unwrap(),
            max_work,
            max_scratch_bytes: layout.total_bytes(),
        };
        for staged in [false, true] {
            let mut scratch = DecodeScratch::new(&layout).unwrap();
            scratch.outcomes.truncate(fields[2].parse().unwrap());
            let request = DecodeRequest {
                local: &fixture.local,
                remote: fixture.view(),
                candidates: &[1],
                plan: &plan,
                limits: &limits,
            };
            let result = if staged {
                DecodeJob::new(request, &decoder, &mut scratch).and_then(DecodeJob::finish)
            } else {
                decode_into(request, &decoder, &mut scratch)
            };
            let observed = match result {
                Err(error) => format!("{error:?}"),
                Ok(report) => {
                    assert_eq!(
                        outcomes(&report),
                        [
                            Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
                            Outcome::Equal
                        ]
                    );
                    assert_eq!(report.work, WorkUnits(8));
                    "DegreeExceedsBudget,Equal".to_owned()
                }
            };
            assert_eq!(
                observed, fields[3],
                "V2 failure vector {} staged={staged}",
                fields[0]
            );
        }
    }
}

fn check_raw_candidate_count() {
    let plan = DecodePlan::v2();
    let fixture = Fixture::new(&[&[1]], false);
    let (_, layout) = fixture.layout(plan, 1, 3);
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let mut scratch = DecodeScratch::new(&layout).unwrap();
    scratch.outcomes.clear();
    let limits = DecodeLimits {
        max_output_per_bucket: 1,
        max_candidate_inputs: 1,
        max_work: WorkUnits(u64::MAX),
        max_scratch_bytes: 0,
    };
    let request = DecodeRequest {
        local: &fixture.local,
        remote: fixture.view(),
        candidates: &[1, 1, 0],
        plan: &plan,
        limits: &limits,
    };
    assert_eq!(
        DecodeJob::new(request, &decoder, &mut scratch).map(|_| ()),
        Err(DecodeError::CandidateLimitExceeded),
        "raw count before dedup and short scratch"
    );
    assert_eq!(
        decode_into(request, &decoder, &mut scratch).map(|_| ()),
        Err(DecodeError::CandidateLimitExceeded)
    );
}

fn odd_words(ids: &[u64], capacity: usize) -> Vec<u64> {
    let mut words = vec![0; capacity];
    for &id in ids {
        let square = crate::field::reference::mul::<Gf64>(id, id);
        let mut power = id;
        for word in &mut words {
            *word ^= power;
            power = crate::field::reference::mul::<Gf64>(power, square);
        }
    }
    words
}
