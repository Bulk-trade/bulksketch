//! Public explicit-V3 probes and naturally reached leaves, including malformed rows.
#![forbid(unsafe_code)]
use {
    super::*,
    crate::{
        BackendId, BackendRequest, DecodeLimits, DecodePlan, FrozenSketch, Gf64, MutableSketch,
        ParseLimits, ShapeLimits, SketchShape, SketchView, WorkUnits,
        field::reference,
        types::small_degree_observer::{self as observer, Fault},
    },
    std::sync::Arc,
};

#[derive(Debug, PartialEq, Eq)]
enum Owned {
    Equal,
    Decoded(Vec<u64>),
    Failed(DecodeFailure),
}
type RunResult = (Vec<Owned>, Vec<(Stage, u64)>);
struct Fixture {
    local: FrozenSketch<Gf64>,
    bytes: Vec<u8>,
    zero: bool,
}
fn odd(roots: &[u64], capacity: usize) -> Vec<u64> {
    let mut words = vec![0; capacity];
    for &root in roots {
        let step = reference::mul::<Gf64>(root, root);
        let mut power = root;
        for word in &mut words {
            *word ^= power;
            power = reference::mul::<Gf64>(power, step);
        }
    }
    words
}
impl Fixture {
    fn new(rows: &[Vec<u64>], zero: bool) -> Self {
        let capacities: Vec<_> = rows.iter().map(Vec::len).collect();
        let shape = Arc::new(
            SketchShape::<Gf64>::new(
                &capacities,
                &ShapeLimits {
                    max_wire_bytes: 100000,
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
        let mut bytes = local.encoded_v1().unwrap().to_vec();
        let flags = 24 + 2 * rows.len();
        bytes[flags] = u8::from(zero);
        for (out, &word) in bytes[flags + rows.len().div_ceil(8)..]
            .chunks_exact_mut(8)
            .zip(rows.iter().flatten())
        {
            out.copy_from_slice(&word.to_le_bytes());
        }
        Self { local, bytes, zero }
    }
    fn run(
        &self,
        beta: usize,
        hints: &[u64],
        plan: DecodePlan,
        decoder: &Decoder<Gf64>,
        limit: Option<u64>,
    ) -> Result<RunResult, DecodeError> {
        let capacities = self.local.shape().capacities();
        let budgets: Vec<_> = (0..capacities.len())
            .map(|i| beta.checked_sub(usize::from(self.zero && i == 0)))
            .collect();
        let (bound, layout) = plan
            .complete_bound(capacities, &budgets, beta, hints.len())
            .unwrap();
        let limits = DecodeLimits {
            max_output_per_bucket: beta,
            max_candidate_inputs: hints.len(),
            max_work: WorkUnits(limit.unwrap_or(bound.0)),
            max_scratch_bytes: layout.total_bytes(),
        };
        let view = SketchView::parse(
            &self.bytes,
            &ParseLimits {
                max_wire_bytes: 100000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap();
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        scratch.words.fill(0xdead_beef_cafe_babe);
        let mut job = DecodeJob::new(
            DecodeRequest {
                local: &self.local,
                remote: view,
                candidates: hints,
                plan: &plan,
                limits: &limits,
            },
            decoder,
            &mut scratch,
        )?;
        let mut stages = Vec::new();
        while job.next_stage().is_some() {
            let JobState::Row { layout, .. } = &job.state else {
                unreachable!()
            };
            let row_layout = RowLayout::new(layout.difference, layout.roots).unwrap();
            let before = words(&mut job.workspace, &row_layout);
            let inversions = observer::snapshot().inversions.len();
            match job.run_next() {
                StageProgress::Completed { stage, work, .. } => stages.push((stage, work.0)),
                StageProgress::Failed(error) => {
                    // Tests use single-row charged stages: no later Compare can fail here.
                    if capacities.len() == 1 {
                        assert_eq!(
                            words(&mut job.workspace, &row_layout),
                            before,
                            "denied stage changed arena"
                        );
                        assert_eq!(
                            observer::snapshot().inversions.len(),
                            inversions,
                            "denied stage entered inversion"
                        );
                    }
                    assert_eq!(job.run_next(), StageProgress::Failed(error));
                    return job.finish().map(|_| unreachable!());
                }
            }
        }
        let report = job.finish()?;
        let outcomes = (0..capacities.len())
            .map(|i| match report.outcome(i).unwrap() {
                DecodeOutcome::Equal => Owned::Equal,
                DecodeOutcome::Decoded { ids } => Owned::Decoded(ids.to_vec()),
                DecodeOutcome::Failed { reason } => Owned::Failed(reason),
            })
            .collect();
        Ok((outcomes, stages))
    }
}
fn words(workspace: &mut DecodeWorkspace<'_>, layout: &RowLayout) -> Vec<u64> {
    let (_, difference, row) = workspace.row(layout);
    let mut result = Vec::new();
    for values in [
        difference,
        row.syndromes,
        row.bm,
        row.polynomials,
        row.factors,
        row.square_table,
        row.verification,
        row.roots,
    ] {
        result.extend_from_slice(values);
    }
    for raw in row.raw {
        result.extend([raw.lo, raw.hi]);
    }
    for frame in row.stack {
        result.extend([
            frame.coefficient_start,
            frame.coefficient_len,
            u64::from(frame.next_direction),
            u64::from(frame.split_checked),
        ]);
    }
    result.push(u64::from(row.basis.len));
    if let Some(basis) = &row.basis.directions {
        result.extend_from_slice(basis);
    }
    result
}
fn decoder() -> Decoder<Gf64> {
    Decoder::new(BackendRequest::Auto, 0xd6e8_feb8_6659_fd93).unwrap()
}

#[test]
fn guard_order_inversions_and_late_verification() {
    for (beta, original, cases) in [
        (
            3,
            vec![0, 6, 0x12, 0x7e, 0x102, 0x70e],
            vec![
                (vec![0, 6, 0x12, 0x7f, 0x105, 0x70e], vec![7], 1139),
                (vec![0, 6, 0x12, 0x7e, 0x103, 0x70e], vec![7, 9], 1443),
                (vec![0, 6, 0x12, 0x7e, 0x102, 0x70f], vec![7, 9], 2620),
            ],
        ),
        (
            4,
            vec![0, 0x22, 0x356, 0x2d5a, 0x30506, 0x2b636a, 0x3705076],
            vec![
                (
                    vec![0, 0x22, 0x356, 0x2d5a, 0x30507, 0x2b6371, 0x3705076],
                    vec![9],
                    1581,
                ),
                (
                    vec![0, 0x22, 0x356, 0x2d5a, 0x30506, 0x2b636b, 0x3705076],
                    vec![9, 11],
                    1897,
                ),
                (
                    vec![0, 0x22, 0x356, 0x2d5a, 0x30506, 0x2b636a, 0x3705077],
                    vec![9, 11],
                    4552,
                ),
            ],
        ),
    ] {
        let guard = if beta == 3 {
            Stage::GuardThree
        } else {
            Stage::GuardFour
        };
        for (row, indices, expected_work) in cases {
            let fixture = Fixture::new(&[row], false);
            observer::reset(Fault::None, false);
            let (outcome, stages) = fixture
                .run(beta, &[], DecodePlan::v3(), &decoder(), None)
                .unwrap();
            let observations = observer::finish();
            assert_eq!(
                observations
                    .residuals
                    .iter()
                    .filter(|(s, _)| *s == guard)
                    .map(|(_, i)| *i)
                    .collect::<Vec<_>>(),
                indices
            );
            assert!(
                observations
                    .inversions
                    .iter()
                    .all(|(s, _)| !matches!(s, Stage::GuardThree | Stage::GuardFour)),
                "guard inversions must be zero"
            );
            assert_eq!(
                stages.last().unwrap().1,
                expected_work,
                "isolated guard/late-mismatch work"
            );
            assert!(!stages.iter().any(|(s, _)| *s == Stage::Canonicalization));
            assert_eq!(
                outcome,
                fixture
                    .run(beta, &[], DecodePlan::v2(), &decoder(), None)
                    .unwrap()
                    .0
            );
            assert_eq!(
                outcome,
                vec![Owned::Failed(DecodeFailure::DegreeExceedsBudget)]
            );
        }
        let fixture = Fixture::new(&[original], false);
        observer::reset(Fault::None, false);
        let (_, stages) = fixture
            .run(beta, &[], DecodePlan::v3(), &decoder(), None)
            .unwrap();
        let observations = observer::finish();
        if beta == 4 {
            assert_eq!(observations.selections, vec![3], "quartic kernel selection");
        }
        assert_eq!(
            observations
                .residuals
                .iter()
                .filter(|(s, _)| *s == guard)
                .map(|(_, i)| *i)
                .collect::<Vec<_>>(),
            if beta == 3 { vec![7, 9] } else { vec![9, 11] }
        );
        for (_, threshold) in stages {
            for limit in [threshold - 1, threshold] {
                observer::reset(Fault::None, false);
                let result = fixture.run(beta, &[], DecodePlan::v3(), &decoder(), Some(limit));
                let observation = observer::finish();
                if limit < if beta == 3 { 939 } else { 2489 } {
                    assert_eq!(result, Err(DecodeError::WorkLimitExceeded));
                }
                if limit < if beta == 3 { 201 } else { 298 } {
                    assert!(
                        observation.inversions.is_empty(),
                        "denied Newton must leave zero inversions"
                    );
                }
            }
        }
    }
}

#[test]
fn natural_hinted_leaves_and_same_factor_fallback() {
    for (roots, c, beta, hints, leaf) in [
        (vec![1, 2, 4, 8, 15], 6, 5, vec![8, 15], Stage::LeafThree),
        (vec![1, 2, 3, 4, 8, 12], 7, 6, vec![8, 12], Stage::LeafFour),
    ] {
        let fixture = Fixture::new(&[odd(&roots, c)], false);
        for fault in [
            Fault::None,
            Fault::SolverMiss,
            Fault::Duplicate,
            Fault::Zero,
            Fault::Wrong,
            Fault::Incomplete,
        ] {
            observer::reset(fault, true);
            let (outcomes, stages) = fixture
                .run(beta, &hints, DecodePlan::v3(), &decoder(), None)
                .unwrap();
            let observations = observer::finish();
            assert_eq!(outcomes, vec![Owned::Decoded(roots.clone())]);
            let at = stages
                .iter()
                .position(|(s, _)| *s == leaf)
                .expect("natural residual leaf");
            assert_eq!(
                stages[at - 1].0,
                Stage::Deflation,
                "closed leaf precedes reducer"
            );
            assert_eq!(
                stages.iter().filter(|(s, _)| *s == leaf).count(),
                1,
                "no leaf replay"
            );
            assert_eq!(
                observations
                    .solvers
                    .iter()
                    .filter(|(_, factor)| *factor)
                    .count(),
                1
            );
            if fault == Fault::None {
                assert!(observations.certificates.contains(&(true, true)));
                assert_eq!(
                    stages.last().unwrap().1,
                    if beta == 5 { 2990 } else { 4892 },
                    "hinted complete work"
                );
                for &(_, threshold) in stages.iter().filter(|(s, _)| {
                    matches!(
                        s,
                        Stage::LeafThree
                            | Stage::LeafFour
                            | Stage::FactorVerification
                            | Stage::Verification
                            | Stage::Canonicalization
                    )
                }) {
                    for limit in [threshold - 1, threshold] {
                        observer::reset(Fault::None, false);
                        let result =
                            fixture.run(beta, &hints, DecodePlan::v3(), &decoder(), Some(limit));
                        observer::finish();
                        if limit < stages.last().unwrap().1 {
                            assert_eq!(result, Err(DecodeError::WorkLimitExceeded));
                        } else {
                            assert_eq!(result.unwrap().0, outcomes);
                        }
                    }
                }
                assert!(!stages.iter().any(|(s, _)| *s == Stage::ReducerPreparation));
            } else {
                let offset = if fault == Fault::SolverMiss { 1 } else { 2 };
                assert_eq!(
                    stages[at + offset].0,
                    Stage::ReducerPreparation,
                    "same-factor fallback"
                );
                assert!(stages.iter().any(|(s, _)| *s == Stage::AffinePreparation));
                assert!(
                    !observations
                        .certificates
                        .iter()
                        .any(|&(factor, valid)| factor && valid),
                    "invalid returned roots must fail certificate"
                );
            }
            assert_eq!(
                outcomes,
                fixture
                    .run(beta, &hints, DecodePlan::v2(), &decoder(), None)
                    .unwrap()
                    .0
            );
            println!(
                "DEG34_HINT beta={beta} fault={fault:?} work={}",
                stages.last().unwrap().1
            );
        }
        let (_, stages) = fixture
            .run(beta, &roots, DecodePlan::v3(), &decoder(), None)
            .unwrap();
        assert!(
            !stages
                .iter()
                .any(|(s, _)| matches!(s, Stage::LeafThree | Stage::LeafFour)),
            "full candidate coverage needs no leaf"
        );
    }
}

#[test]
fn affine_children_collision_and_routing() {
    let children: Vec<_> = [3, 2, 1, 7, 11, 19, 35, 67, 131]
        .into_iter()
        .map(|r| 2 * r + 1)
        .collect();
    let mut expected = children.clone();
    expected.sort_unstable();
    let fixture = Fixture::new(&[odd(&children, 18)], false);
    for fault in [Fault::None, Fault::SolverMiss, Fault::Wrong] {
        observer::reset(fault, true);
        let (outcomes, stages) = fixture
            .run(18, &[], DecodePlan::v3(), &decoder(), None)
            .unwrap();
        let observations = observer::finish();
        assert_eq!(outcomes, vec![Owned::Decoded(expected.clone())]);
        let split = stages
            .iter()
            .position(|(s, _)| *s == Stage::AffineSplit)
            .expect("natural affine splitting");
        let leaf = stages
            .iter()
            .position(|(s, _)| *s == Stage::LeafFour)
            .expect("natural affine quartic child leaf");
        assert!(leaf > split);
        assert!(observations.solvers.iter().any(|(_, f)| *f));
        assert_eq!(
            stages
                .iter()
                .filter(|(s, _)| *s == Stage::AffinePreparation)
                .count(),
            1,
            "reuse affine map after miss"
        );
        println!(
            "DEG34_CHILD fault={fault:?} work={} stages={stages:?}",
            stages.last().unwrap().1
        );
    }
    let cubic_children = vec![
        0x910a2dec89025cc1,
        0x975835de1c9756cf,
        0x1d0b14e4db018fed,
        0x6e73e372e2338acb,
        0x63033b0ca389c35b,
        0xbd64a5d9adefe001,
        0x63cbe1e459320dd7,
        0x9e5651b0ef953637,
        0xaeaf52febe706065,
    ];
    let cubic = Fixture::new(&[odd(&cubic_children, 18)], false);
    let (outcomes, stages) = cubic
        .run(18, &[], DecodePlan::v3(), &decoder(), None)
        .unwrap();
    let mut sorted = cubic_children;
    sorted.sort_unstable();
    assert_eq!(outcomes, vec![Owned::Decoded(sorted)]);
    assert!(
        stages
            .iter()
            .position(|(s, _)| *s == Stage::AffineSplit)
            .expect("cubic fixture must split")
            < stages
                .iter()
                .position(|(s, _)| *s == Stage::LeafThree)
                .unwrap_or_else(|| panic!("natural cubic child: {stages:?}"))
    );
    let wrong_bucket = Fixture::new(&[odd(&children, 18), vec![0; 18]], false);
    let (outcomes, stages) = wrong_bucket
        .run(18, &[], DecodePlan::v3(), &decoder(), None)
        .unwrap();
    assert_eq!(
        outcomes,
        vec![Owned::Failed(DecodeFailure::InvalidLocator), Owned::Equal]
    );
    assert!(stages.iter().any(|(s, _)| *s == Stage::FactorVerification));
    assert!(
        !stages.iter().any(|(s, _)| *s == Stage::Canonicalization),
        "routing rejection precedes canonicalization"
    );
    let five = Fixture::new(&[odd(&[1, 3, 5, 9, 15], 6), vec![0; 6]], false);
    let (outcomes, stages) = five
        .run(5, &[], DecodePlan::v3(), &decoder(), None)
        .unwrap();
    assert_eq!(
        outcomes,
        vec![Owned::Failed(DecodeFailure::InvalidLocator), Owned::Equal]
    );
    assert!(!stages.iter().any(|(s, _)| *s == Stage::Canonicalization));
    // S1=0 skips tiny probes in this independently constructed late coincidence.
    let roots: Vec<_> = (1..=15)
        .map(|r| r << 4)
        .chain([0x1000, 0x2000, 0x4000])
        .collect();
    let collision = Fixture::new(&[odd(&roots, 18)], false);
    observer::reset(Fault::None, false);
    let (outcomes, stages) = collision
        .run(18, &[], DecodePlan::v3(), &decoder(), None)
        .unwrap();
    let observation = observer::finish();
    assert_eq!(outcomes, vec![Owned::Decoded(roots)]);
    assert!(
        stages
            .iter()
            .position(|(s, _)| *s == Stage::LeafThree)
            .unwrap()
            < stages
                .iter()
                .position(|(s, _)| *s == Stage::BerlekampMassey)
                .unwrap()
    );
    assert!(observation.certificates.contains(&(false, true)));
    assert!(
        stages
            .iter()
            .filter(|(s, _)| *s == Stage::Verification)
            .count()
            >= 2,
        "late coincidence must fail full verification before fallback"
    );
}

#[test]
fn capacity_zero_seed_and_backend_parity() {
    let mut cases = 0;
    for c in 1..=6 {
        for roots in [vec![1, 2, 3], vec![1, 2, 4, 7]] {
            for zero in [false, true] {
                let mut expected = roots.clone();
                if zero {
                    expected.insert(0, 0);
                }
                let fixture = Fixture::new(&[odd(&roots, c)], zero);
                let beta = c;
                let baseline = fixture
                    .run(beta, &[], DecodePlan::v2(), &decoder(), None)
                    .unwrap()
                    .0;
                let mut previous = None;
                for backend in [
                    BackendId::Portable,
                    BackendId::Pclmul,
                    BackendId::Vpclmul512,
                ] {
                    let Ok(decoder) = Decoder::new(BackendRequest::Force(backend), 0x55) else {
                        continue;
                    };
                    let observed = fixture
                        .run(beta, &[], DecodePlan::v3(), &decoder, None)
                        .unwrap();
                    assert_eq!(observed.0, baseline, "small capacity outcome c={c}");
                    if expected.len() <= c {
                        assert_eq!(observed.0, vec![Owned::Decoded(expected.clone())]);
                        let leaf = if roots.len() == 3 {
                            Stage::LeafThree
                        } else {
                            Stage::LeafFour
                        };
                        assert!(
                            observed.1.iter().any(|(s, _)| *s == leaf),
                            "available-word small-capacity probe must execute"
                        );
                        assert!(!observed.1.iter().any(|(s, _)| *s == Stage::BerlekampMassey));
                    }
                    if let Some(previous) = &previous {
                        assert_eq!(&observed, previous, "backend stages/work parity");
                    }
                    previous = Some(observed);
                    cases += 1;
                }
            }
        }
    }
    let roots = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048];
    let fixture = Fixture::new(&[odd(&roots, 18)], false);
    for seed in [0, 1, 0x55, u64::MAX] {
        let d = Decoder::new(BackendRequest::Auto, seed).unwrap();
        assert_eq!(
            fixture.run(18, &[], DecodePlan::v3(), &d, None).unwrap().0,
            vec![Owned::Decoded(roots.to_vec())]
        );
    }
    let zero_only = Fixture::new(&[vec![0; 6]], true);
    let (_, stages) = zero_only
        .run(6, &[], DecodePlan::v3(), &decoder(), None)
        .unwrap();
    assert!(
        !stages
            .iter()
            .any(|(s, _)| matches!(s, Stage::GuardThree | Stage::GuardFour))
    );
    assert_eq!(
        zero_only
            .run(0, &[], DecodePlan::v3(), &decoder(), None)
            .unwrap()
            .0,
        vec![Owned::Failed(DecodeFailure::DegreeExceedsBudget)]
    );
    println!("DEG34_CAPACITY_BACKEND_CASES {cases}");
}
