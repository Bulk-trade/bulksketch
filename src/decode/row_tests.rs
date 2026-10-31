//! Canonical nonzero rows; zero accounting and Compare belong to the request job.
#![forbid(unsafe_code)]
use {
    super::{
        bm_tests::syndromes,
        row::{RowBudget, RowDecoder, RowExecution, RowInput, RowResult},
        scratch::{FactorFrame, RowWorkspace, SplitterBasis},
        stages::BinaryDecoder,
    },
    crate::{
        backend::portable::Portable,
        field::{
            BinaryField, Gf64,
            tiny::{Gf4, Gf16, Gf256, Gf65536},
        },
        types::{DecodeError, DecodeFailure, RawProduct, Stage, WorkMeter, WorkUnits},
    },
};

pub(super) struct Arena {
    syndromes: Vec<u64>,
    bm: Vec<u64>,
    polynomials: Vec<u64>,
    factors: Vec<u64>,
    square_table: Vec<u64>,
    verification: Vec<u64>,
    roots: Vec<u64>,
    raw: Vec<RawProduct>,
    stack: Vec<FactorFrame>,
    basis: SplitterBasis,
}
impl Arena {
    pub(super) fn new(capacity: usize, budget: usize, garbage: u64) -> Self {
        let width = budget + 1;
        Self {
            basis: SplitterBasis::default(),
            syndromes: vec![garbage; 2 * capacity + 1],
            bm: vec![garbage; 4 * (capacity + 1)],
            polynomials: vec![garbage; if budget == 0 { 0 } else { 8 * width }],
            factors: vec![garbage; if budget == 0 { 0 } else { 2 * width * width }],
            square_table: vec![garbage; budget * (budget / 2)],
            verification: vec![garbage; capacity],
            roots: vec![garbage; budget],
            raw: vec![
                RawProduct {
                    lo: garbage,
                    hi: garbage
                };
                if budget == 0 { 0 } else { 2 * (budget + 2) }
            ],
            stack: vec![
                FactorFrame {
                    coefficient_start: garbage,
                    coefficient_len: garbage,
                    next_direction: 123,
                    split_checked: 123
                };
                budget
            ],
        }
    }
    pub(super) fn workspace(&mut self) -> RowWorkspace<'_> {
        RowWorkspace {
            syndromes: &mut self.syndromes,
            bm: &mut self.bm,
            polynomials: &mut self.polynomials,
            factors: &mut self.factors,
            square_table: &mut self.square_table,
            verification: &mut self.verification,
            roots: &mut self.roots,
            raw: &mut self.raw,
            stack: &mut self.stack,
            basis: &mut self.basis,
        }
    }
}
#[derive(Debug, PartialEq, Eq)]
pub(super) enum Outcome {
    Equal,
    Decoded(Vec<u64>),
    Failed(DecodeFailure),
}
pub(super) fn own(result: &RowResult<'_>) -> Outcome {
    match result {
        RowResult::Equal => Outcome::Equal,
        RowResult::Decoded(r) => Outcome::Decoded(r.to_vec()),
        RowResult::Failed(f) => Outcome::Failed(*f),
    }
}
pub(super) fn odd<F: BinaryField>(roots: &[u64], c: usize) -> Vec<u64> {
    syndromes::<F>(roots, c)
        .into_iter()
        .skip(1)
        .step_by(2)
        .collect()
}
type Progress = (Stage, usize, usize, usize, usize);

fn decode<F: BinaryField>(
    values: &[u64],
    budget: usize,
    hints: &[u64],
    garbage: u64,
) -> (Outcome, u64, Vec<Progress>) {
    let mut arena = Arena::new(values.len(), budget, garbage);
    let mut w = arena.workspace();
    let mut execution = <BinaryDecoder as RowDecoder<F, Portable>>::begin(RowBudget {
        nonzero: budget,
        total: budget,
    });
    let bound =
        super::work::WorkScheduleV1::row_bound(values.len(), budget, budget, hints.len()).unwrap();
    let mut meter = WorkMeter::new(bound);
    let input = RowInput {
        difference: values,
        candidates: hints,
    };
    let mut progress = vec![];
    while execution.next_stage().is_some() {
        let p = execution.run_next(input, &mut w, &mut meter).unwrap();
        progress.push((
            p.stage,
            p.locator_degree,
            p.candidate_hits,
            p.trace_attempts,
            p.gcd_degree,
        ));
    }
    let result = own(&execution.finish(input, &mut w, &mut meter).unwrap());
    (result, meter.used().0, progress)
}
fn check<F: BinaryField>(roots: &[u64], c: usize, beta: usize, hints: &[u64]) {
    let values = odd::<F>(roots, c);
    let (result, _, _) = decode::<F>(&values, beta, hints, 0xdead_beef);
    if roots.len() <= beta {
        let expected = if roots.is_empty() {
            Outcome::Equal
        } else {
            Outcome::Decoded(roots.to_vec())
        };
        assert_eq!(
            result,
            expected,
            "exact recovery bits={} c={c} beta={beta} roots={roots:?} hints={hints:?}",
            F::BITS
        );
    } else if roots.len() <= 2 * c - beta {
        assert!(
            matches!(result, Outcome::Failed(_)),
            "protected interval bits={} c={c} beta={beta} roots={roots:?} hints={hints:?} \
             result={result:?}",
            F::BITS
        );
    }
    match result {
        Outcome::Equal => assert!(values.iter().all(|&s| s == 0), "equal re-encoding"),
        Outcome::Decoded(answer) => {
            assert!(answer.len() <= beta);
            assert_eq!(odd::<F>(&answer, c), values, "full independent re-encoding");
            assert!(answer.windows(2).all(|p| p[0] < p[1]));
        }
        Outcome::Failed(_) => {}
    }
}
fn decode_corpus<F: BinaryField>(caps: &[usize]) {
    let mut seed = 0x534b_4e43_4c34_0002u64;
    for &c in caps {
        for beta in [c.min(64), c / 2] {
            for d in [0, 1, 2, 3, 4, 8, 16, 32, 48, 64, beta + 1, 2 * c - beta] {
                if d > beta && d != beta + 1 && d != 2 * c - beta {
                    continue;
                }
                let mut roots = vec![];
                while roots.len() < d {
                    seed ^= seed << 13;
                    seed ^= seed >> 7;
                    seed ^= seed << 17;
                    let x = seed & F::MASK;
                    if x != 0 && !roots.contains(&x) {
                        roots.push(x);
                    }
                }
                roots.sort_unstable();
                let partial = roots.iter().step_by(2).copied().collect::<Vec<_>>();
                for hints in [&[][..], partial.as_slice(), roots.as_slice()] {
                    check::<F>(&roots, c, beta, hints);
                }
            }
        }
    }
}
#[test]
fn decode_tiny_exhaustive() {
    fn enumerate<F: BinaryField>(capacities: &[usize]) {
        for mask in 0..1usize << F::MASK {
            let roots = (1..=F::MASK)
                .filter(|&x| mask >> (x - 1) & 1 != 0)
                .collect::<Vec<_>>();
            for &c in capacities {
                for beta in 0..=c {
                    let mut partial = roots.iter().step_by(2).copied().collect::<Vec<_>>();
                    let wrong = (1..=F::MASK).find(|x| !roots.contains(x));
                    if let Some(x) = wrong {
                        partial.push(x);
                        partial.sort_unstable();
                    }
                    for hints in [&[][..], roots.as_slice(), partial.as_slice()] {
                        check::<F>(&roots, c, beta, hints);
                    }
                }
            }
        }
    }
    enumerate::<Gf4>(&[1, 2, 3]);
    enumerate::<Gf16>(&[1, 2, 3, 4]);
    // Real alias outside the protected interval: 1 XOR 2 = 3 at c=beta=1.
    assert_eq!(
        decode::<Gf4>(&odd::<Gf4>(&[1, 2], 1), 1, &[], 7).0,
        Outcome::Decoded(vec![3]),
        "retained GF4 beyond-bound alias"
    );
}
#[test]
fn decode_broad_corpora() {
    for a in 1..=255 {
        check::<Gf256>(&[a], 2, 2, &[]);
        for b in a + 1..=255 {
            check::<Gf256>(&[a, b], 2, 2, &[a]);
            check::<Gf256>(&[a, b], 2, 1, &[]);
        }
    }
    for a in 1..=16 {
        for b in a + 1..=16 {
            for d in b + 1..=16 {
                check::<Gf256>(&[a, b, d], 4, 3, &[a, b]);
                check::<Gf256>(&[a, b, d], 4, 2, &[a, b]);
            }
        }
    }

    decode_corpus::<Gf65536>(&[1, 2, 4, 8, 18]);
    decode_corpus::<Gf64>(&[18, 72, 89]);
    let roots = (1..=20).collect::<Vec<_>>();
    for d in 17..=20 {
        check::<Gf64>(&roots[..d], 18, 16, &roots[..8]);
    }
}
#[test]
fn candidates_and_full_verification() {
    for hints in [vec![], vec![1, 2], vec![1, 2, 3, 4], vec![2, 5, 6, 8]] {
        check::<Gf16>(&[1, 2, 3, 4], 4, 4, &hints);
    }
    let values = odd::<Gf16>(&[1, 2], 2);
    let mut arena = Arena::new(2, 2, 9);
    let mut w = arena.workspace();
    let input = RowInput {
        difference: &values,
        candidates: &[],
    };
    let mut e = <BinaryDecoder as RowDecoder<Gf16, Portable>>::begin(RowBudget {
        nonzero: 2,
        total: 2,
    });
    let mut meter = WorkMeter::new(WorkUnits(u64::MAX));
    while e.next_stage() != Some(Stage::Verification) {
        e.run_next(input, &mut w, &mut meter).unwrap();
    }
    // Fault injection at the verifier's seam: same S1, different S3.
    w.roots[..2].copy_from_slice(&[4, 7]);
    assert_eq!(
        own(&e.finish(input, &mut w, &mut meter).unwrap()),
        Outcome::Failed(DecodeFailure::VerificationFailed),
        "every stored syndrome must be checked"
    );
}
#[test]
fn work_and_stage_boundaries() {
    check_singleton_work();
    check_root_work();
    check_zero_slot_work();
}
#[test]
fn bm_entry_exhaustion_preserves_workspace() {
    let input = RowInput {
        difference: &[1],
        candidates: &[],
    };
    let budget = RowBudget {
        nonzero: 1,
        total: 1,
    };
    for allowance in [3, 143] {
        let mut arena = Arena::new(1, 1, 0xd1e2_f3a4_b5c6_8798);
        for (index, word) in arena.bm.iter_mut().enumerate() {
            *word = 0xa1b2_c3d4_e5f6_8700 + u64::try_from(index).unwrap();
        }
        let mut workspace = arena.workspace();
        let mut execution = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(budget);
        let mut meter = WorkMeter::new(WorkUnits(allowance));
        execution
            .run_next(input, &mut workspace, &mut meter)
            .unwrap();
        assert_eq!(meter.used(), WorkUnits(3));
        assert_eq!(execution.next_stage(), Some(Stage::BerlekampMassey));
        let before = workspace_snapshot(&workspace);
        assert_eq!(
            execution
                .run_next(input, &mut workspace, &mut meter)
                .map(|p| p.stage),
            Err(DecodeError::WorkLimitExceeded)
        );
        if allowance == 3 {
            assert_eq!(
                workspace_snapshot(&workspace),
                before,
                "exhausted BM entry leaves every workspace byte unchanged"
            );
        }
        assert_eq!(
            meter.used(),
            WorkUnits(allowance),
            "BM charges one position at a time"
        );
        assert_eq!(execution.next_stage(), None);
        assert!(matches!(
            execution.finish(input, &mut workspace, &mut meter),
            Err(DecodeError::WorkLimitExceeded)
        ));
    }
}
fn workspace_snapshot(workspace: &RowWorkspace<'_>) -> [Vec<u8>; 9] {
    let words = |values: &[u64]| {
        values
            .iter()
            .flat_map(|value| value.to_ne_bytes())
            .collect()
    };
    [
        words(workspace.syndromes),
        words(workspace.bm),
        words(workspace.polynomials),
        words(workspace.factors),
        words(workspace.square_table),
        words(workspace.verification),
        words(workspace.roots),
        workspace
            .raw
            .iter()
            .flat_map(|value| [value.lo, value.hi])
            .flat_map(u64::to_ne_bytes)
            .collect(),
        workspace
            .stack
            .iter()
            .flat_map(|frame| {
                frame
                    .coefficient_start
                    .to_ne_bytes()
                    .into_iter()
                    .chain(frame.coefficient_len.to_ne_bytes())
                    .chain(frame.next_direction.to_ne_bytes())
                    .chain(frame.split_checked.to_ne_bytes())
            })
            .collect(),
    ]
}
fn check_singleton_work() {
    assert_eq!(
        decode::<Gf64>(&[0], 0, &[], 123).1,
        0,
        "equal rows pay Compare upstairs only"
    );
    let values = [1];
    let input = RowInput {
        difference: &values,
        candidates: &[],
    };
    let budget = RowBudget {
        nonzero: 1,
        total: 1,
    };
    let expected = [
        (Stage::Reconstruction, 3),
        (Stage::BerlekampMassey, 280),
        (Stage::CandidateEvaluation, 0),
        (Stage::Deflation, 4),
        (Stage::Leaf, 1),
        (Stage::Verification, 7),
        (Stage::Canonicalization, 1),
    ];
    let mut arena = Arena::new(1, 1, 99);
    let mut w = arena.workspace();
    let mut e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(budget);
    let mut meter = WorkMeter::new(WorkUnits(296));
    let mut prefix = 0;
    for &(stage, cost) in &expected {
        assert_eq!(e.next_stage(), Some(stage));
        let p = e.run_next(input, &mut w, &mut meter).unwrap();
        assert_eq!(p.stage, stage);
        prefix += cost;
        assert_eq!(
            meter.used(),
            WorkUnits(prefix),
            "hand-derived stage charge {stage:?}"
        );
    }
    assert_eq!(
        own(&e.finish(input, &mut w, &mut meter).unwrap()),
        Outcome::Decoded(vec![1])
    );
    for boundary in 0..expected.len() {
        let mut arena = Arena::new(1, 1, 123);
        let mut w = arena.workspace();
        let mut e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(budget);
        let mut m = WorkMeter::new(WorkUnits(u64::MAX));
        for _ in 0..boundary {
            e.run_next(input, &mut w, &mut m).unwrap();
        }
        let before = w.syndromes.to_vec();
        let before_all = workspace_snapshot(&w);
        let mut exhausted = WorkMeter::new(WorkUnits(0));
        assert_eq!(
            exhausted.charge(WorkUnits(1)),
            Err(DecodeError::WorkLimitExceeded)
        );
        assert_eq!(
            e.run_next(input, &mut w, &mut exhausted).map(|p| p.stage),
            Err(DecodeError::WorkLimitExceeded),
            "charge precedes {boundary}"
        );
        assert_eq!(
            w.syndromes, before,
            "failed charge does not execute reconstruction"
        );
        assert_eq!(
            workspace_snapshot(&w),
            before_all,
            "failed charge leaves every workspace segment unchanged at {boundary}"
        );
        assert_eq!(e.next_stage(), None);
        assert!(
            matches!(
                e.finish(input, &mut w, &mut m),
                Err(DecodeError::WorkLimitExceeded)
            ),
            "terminal error publishes nothing"
        );
    }
}
fn check_root_work() {
    let sums = odd::<Gf4>(&[1, 2, 3], 3);
    let input3 = RowInput {
        difference: &sums,
        candidates: &[],
    };
    let root_charges = [
        (Stage::Reconstruction, 9),
        (Stage::BerlekampMassey, 912),
        (Stage::CandidateEvaluation, 0),
        (Stage::Deflation, 24),
        (Stage::ReducerPreparation, 78),
        (Stage::Trace, 2242),
        (Stage::Gcd, 640),
        (Stage::FactorDivision, 208),
        (Stage::Leaf, 1),
        (Stage::Leaf, 160),
        (Stage::Verification, 31),
        (Stage::Canonicalization, 9),
    ];
    let mut arena3 = Arena::new(3, 3, 111);
    let mut w3 = arena3.workspace();
    let mut e3 = <BinaryDecoder as RowDecoder<Gf4, Portable>>::begin(RowBudget {
        nonzero: 3,
        total: 3,
    });
    let mut m3 = WorkMeter::new(WorkUnits(4314));
    let mut prefix3 = 0;
    for &(stage, cost) in &root_charges {
        assert_eq!(e3.next_stage(), Some(stage));
        e3.run_next(input3, &mut w3, &mut m3).unwrap();
        prefix3 += cost;
        assert_eq!(
            m3.used(),
            WorkUnits(prefix3),
            "hand-derived root charge {stage:?}"
        );
    }
    assert_eq!(
        own(&e3.finish(input3, &mut w3, &mut m3).unwrap()),
        Outcome::Decoded(vec![1, 2, 3])
    );
    for boundary in 4..root_charges.len() {
        let mut a = Arena::new(3, 3, 22);
        let mut w = a.workspace();
        let mut e = <BinaryDecoder as RowDecoder<Gf4, Portable>>::begin(RowBudget {
            nonzero: 3,
            total: 3,
        });
        let mut m = WorkMeter::new(WorkUnits(u64::MAX));
        for _ in 0..boundary {
            e.run_next(input3, &mut w, &mut m).unwrap();
        }
        let before_all = workspace_snapshot(&w);
        let mut exhausted = WorkMeter::new(WorkUnits(0));
        assert_eq!(
            exhausted.charge(WorkUnits(1)),
            Err(DecodeError::WorkLimitExceeded)
        );
        assert_eq!(
            e.run_next(input3, &mut w, &mut exhausted).map(|p| p.stage),
            Err(DecodeError::WorkLimitExceeded),
            "root boundary {boundary}"
        );
        assert_eq!(
            workspace_snapshot(&w),
            before_all,
            "failed root charge leaves every workspace segment unchanged at {boundary}"
        );
        assert!(matches!(
            e.finish(input3, &mut w, &mut m),
            Err(DecodeError::WorkLimitExceeded)
        ));
    }
}
fn check_zero_slot_work() {
    let input = RowInput {
        difference: &[1],
        candidates: &[],
    };
    for (total, expected_work) in [(1, 584), (2, 592)] {
        let mut a = Arena::new(2, 1, 33);
        let e =
            <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(RowBudget { nonzero: 1, total });
        let mut m = WorkMeter::new(WorkUnits(u64::MAX));
        assert_eq!(
            own(&e
                .finish(
                    RowInput {
                        difference: &[1, 1],
                        candidates: &[]
                    },
                    &mut a.workspace(),
                    &mut m
                )
                .unwrap()),
            Outcome::Decoded(vec![1])
        );
        assert_eq!(
            m.used(),
            WorkUnits(expected_work),
            "total beta includes the upstairs zero slot"
        );
    }
    let mut arena = Arena::new(1, 0, 0);
    let mut w = arena.workspace();
    let mut e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(RowBudget {
        nonzero: 0,
        total: 0,
    });
    let mut m = WorkMeter::new(WorkUnits(3));
    e.run_next(input, &mut w, &mut m).unwrap();
    assert!(
        matches!(
            e.finish(input, &mut w, &mut m),
            Err(DecodeError::WorkLimitExceeded)
        ),
        "exhausted BM charge precedes degree failure"
    );
}

#[test]
fn scratch_and_determinism() {
    let values = odd::<Gf64>(&[1, 2, 3, 4, 5, 6, 7, 8], 18);
    let baseline = decode::<Gf64>(&values, 16, &[2, 4, 6], 0);
    for garbage in [1, u64::MAX, 0x1234_5678_9abc_def0] {
        assert_eq!(
            decode::<Gf64>(&values, 16, &[2, 4, 6], garbage),
            baseline,
            "garbage-independent roots, counters and work"
        );
    }
    let mut arena = Arena::new(18, 16, 77);
    let input = RowInput {
        difference: &values,
        candidates: &[],
    };
    let mut w = arena.workspace();
    let mut m = WorkMeter::new(WorkUnits(u64::MAX));
    {
        let mut e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(RowBudget {
            nonzero: 16,
            total: 16,
        });
        for _ in 0..4 {
            e.run_next(input, &mut w, &mut m).unwrap();
        }
    }
    let pointer = w.roots.as_ptr();
    let e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(RowBudget {
        nonzero: 16,
        total: 16,
    });
    match e.finish(input, &mut w, &mut m).unwrap() {
        RowResult::Decoded(r) => {
            assert_eq!(r, &[1, 2, 3, 4, 5, 6, 7, 8]);
            assert_eq!(
                r.as_ptr(),
                pointer,
                "finish borrows exactly the verified prefix"
            );
        }
        _ => panic!("reused workspace must decode"),
    }
    for segment in 0..9 {
        let mut short = Arena::new(18, 16, 17);
        match segment {
            0 => {
                short.syndromes.pop();
            }
            1 => {
                short.bm.pop();
            }
            2 => {
                short.polynomials.pop();
            }
            3 => {
                short.factors.pop();
            }
            4 => {
                short.square_table.pop();
            }
            5 => {
                short.verification.pop();
            }
            6 => {
                short.roots.pop();
            }
            7 => {
                short.raw.pop();
            }
            8 => {
                short.stack.pop();
            }
            _ => unreachable!(),
        }
        let mut e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(RowBudget {
            nonzero: 16,
            total: 16,
        });
        assert_eq!(
            e.run_next(input, &mut short.workspace(), &mut m)
                .map(|p| p.stage),
            Err(DecodeError::ScratchTooSmall),
            "short segment={segment}"
        );
    }
    let empty = vec![0; 18];
    let input = RowInput {
        difference: &empty,
        candidates: &[],
    };
    let e = <BinaryDecoder as RowDecoder<Gf64, Portable>>::begin(RowBudget {
        nonzero: 0,
        total: 1,
    });
    let mut zero = Arena::new(18, 0, u64::MAX);
    assert_eq!(
        own(&e.finish(input, &mut zero.workspace(), &mut m).unwrap()),
        Outcome::Decoded(vec![]),
        "zero-only row returns an empty nonzero slice for upstairs publication"
    );
}
