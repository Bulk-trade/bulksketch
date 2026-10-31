fn send_sync<T: Send + Sync>() {}

use {
    super::*,
    crate::{
        Gf64,
        decode::work::{Charge, WorkScheduleV1},
        types::{DecodeError, DecodeFailure, WorkMeter, WorkUnits},
    },
    api::{Publication, admit},
};

fn limits(beta: usize) -> DecodeLimits {
    DecodeLimits {
        max_output_per_bucket: beta,
        max_candidate_inputs: 10,
        max_work: WorkUnits(u64::MAX),
        max_scratch_bytes: usize::MAX,
    }
}
fn wire_limits() -> ParseLimits {
    ParseLimits {
        max_wire_bytes: 4096,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 1424,
    }
}
fn owned(bytes: &[u8]) -> FrozenSketch<Gf64> {
    FrozenSketch::from_view(
        SketchView::parse(bytes, &wire_limits()).unwrap(),
        &ShapeLimits {
            max_wire_bytes: 4096,
            max_buckets: 16,
            max_capacity_per_bucket: 89,
            max_total_syndrome_words: 1424,
        },
    )
    .unwrap()
}
fn record(capacities: &[u16], zero: bool) -> Vec<u8> {
    let words: usize = capacities.iter().map(|&c| usize::from(c)).sum();
    let payload = capacities.len().div_ceil(8) + 8 * words;
    let mut b = b"SKNC\x01\x01\x01\x00".to_vec();
    b.extend_from_slice(&u16::try_from(capacities.len()).unwrap().to_le_bytes());
    b.extend_from_slice(&0u16.to_le_bytes());
    b.extend_from_slice(&u32::try_from(2 * capacities.len()).unwrap().to_le_bytes());
    b.extend_from_slice(&u32::try_from(payload).unwrap().to_le_bytes());
    b.extend_from_slice(&0u32.to_le_bytes());
    for c in capacities {
        b.extend_from_slice(&c.to_le_bytes());
    }
    b.push(u8::from(zero));
    b.resize(24 + 2 * capacities.len() + payload, 0);
    b
}

#[test]
fn admission_precedence() {
    let local_bytes = record(&[1, 1], false);
    let remote_bytes = record(&[1, 1], true);
    let local = owned(&local_bytes);
    let remote = SketchView::<Gf64>::parse(&remote_bytes, &wire_limits()).unwrap();
    let plan = DecodePlan::v1();
    let (_, layout) = plan
        .complete_bound(&[1, 1], &[None, Some(0)], 0, 1)
        .unwrap();
    for line in include_str!("../../tests/vectors/failure-v1.tsv")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        let fields: Vec<_> = line.split_whitespace().collect();
        let mut caps = limits(0);
        caps.max_candidate_inputs = fields[1].parse().unwrap();
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        scratch.outcomes.truncate(fields[2].parse().unwrap());
        let request = DecodeRequest {
            local: &local,
            remote,
            candidates: &[1],
            plan: &plan,
            limits: &caps,
        };
        let observed = match admit(&request, &scratch) {
            Err(error) => format!("{error:?}"),
            Ok(mut admitted) => {
                assert_eq!(admitted.zero_failures, 1);
                admitted
                    .meter
                    .charge(WorkScheduleV1::cost(Charge::Normalize { inputs: 1 }).unwrap())
                    .unwrap();
                admitted
                    .meter
                    .charge(WorkScheduleV1::cost(Charge::Compare { capacity: 1 }).unwrap())
                    .unwrap();
                let mut publication =
                    Publication::new(scratch.split(&admitted.layout).1, &admitted.layout);
                publication.write(
                    0,
                    DecodeOutcome::Failed {
                        reason: DecodeFailure::DegreeExceedsBudget,
                    },
                    false,
                );
                publication.write(1, DecodeOutcome::Equal, false);
                let report = publication
                    .finish(admitted.meter.used(), admitted.layout.total_bytes())
                    .unwrap();
                assert_eq!(
                    report.outcome(0),
                    Some(DecodeOutcome::Failed {
                        reason: DecodeFailure::DegreeExceedsBudget
                    })
                );
                assert_eq!(report.outcome(1), Some(DecodeOutcome::Equal));
                assert_eq!(report.work, WorkUnits(8));
                assert_eq!(report.bucket_count(), 2);
                assert_eq!(report.outcome(2), None);
                "DegreeExceedsBudget,Equal".to_owned()
            }
        };
        assert_eq!(
            observed, fields[3],
            "{}: request-wide errors suppress row classifications; candidates precede scratch",
            fields[0]
        );
    }
}

#[test]
fn request_error_order() {
    let bytes = record(&[1, 1], false);
    let local = owned(&bytes);
    let wrong_shape = record(&[2, 2], true);
    let plan = DecodePlan::v1();
    let mut caps = limits(2);
    caps.max_candidate_inputs = 0;
    caps.max_work = WorkUnits(0);
    caps.max_scratch_bytes = 0;
    let layout = ScratchLayout::for_plan(&plan, &[1, 1], &[Some(0), Some(0)], 0, 0).unwrap();
    let mut scratch = DecodeScratch::new(&layout).unwrap();
    scratch.outcomes.clear();
    let mut remote = SketchView::parse(&wrong_shape, &wire_limits()).unwrap();
    let mut selected_plan = &plan;
    macro_rules! req {
        () => {
            DecodeRequest {
                local: &local,
                remote,
                candidates: &[1],
                plan: selected_plan,
                limits: &caps,
            }
        };
    }
    assert_eq!(
        admit(&req!(), &scratch).unwrap_err(),
        DecodeError::ShapeMismatch
    );
    remote = SketchView::parse(&bytes, &wire_limits()).unwrap();
    assert_eq!(
        admit(&req!(), &scratch).unwrap_err(),
        DecodeError::InvalidPlan
    );
    caps.max_output_per_bucket = 0;
    assert_eq!(
        admit(&req!(), &scratch).unwrap_err(),
        DecodeError::CandidateLimitExceeded
    );
    caps.max_candidate_inputs = 1;
    assert_eq!(
        admit(&req!(), &scratch).unwrap_err(),
        DecodeError::WorkLimitExceeded,
        "work admission precedes scratch cap and actual storage"
    );
    caps.max_work = WorkUnits(3);
    assert_eq!(
        admit(&req!(), &scratch).unwrap_err(),
        DecodeError::ScratchTooSmall
    );
    let bad_plan = DecodePlan { version: 99 };
    selected_plan = &bad_plan;
    assert_eq!(
        admit(&req!(), &scratch).unwrap_err(),
        DecodeError::InvalidPlan
    );
}

#[test]
fn atomic_publication_and_reuse() {
    let plan = DecodePlan::v1();
    let layout = ScratchLayout::for_plan(&plan, &[1, 1], &[Some(1), Some(1)], 1, 0).unwrap();
    let mut scratch = DecodeScratch::<Gf64>::new(&layout).unwrap();
    let local_bytes = record(&[1, 1], false);
    let mut remote_bytes = local_bytes.clone();
    remote_bytes[29..37].copy_from_slice(&2u64.to_le_bytes());
    let local = owned(&local_bytes);
    let remote = SketchView::parse(&remote_bytes, &wire_limits()).unwrap();
    let mut caps = limits(1);
    caps.max_work = WorkUnits(301);
    let request = DecodeRequest {
        local: &local,
        remote,
        candidates: &[],
        plan: &plan,
        limits: &caps,
    };
    let mut admitted = admit(&request, &scratch).unwrap();
    let mut publication = Publication::new(scratch.split(&admitted.layout).1, &admitted.layout);
    // Known one-root row {2}: model every prescribed charge before supplying its verified result.
    for charge in [
        Charge::Normalize { inputs: 0 },
        Charge::Compare { capacity: 1 },
        Charge::Reconstruct { capacity: 1 },
        Charge::BmStep { budget: 1 },
        Charge::BmStep { budget: 1 },
        Charge::Candidates {
            degree: 1,
            inputs: 0,
        },
        Charge::Deflate { degree: 1 },
        Charge::Leaf { degree: 1 },
        Charge::Verify {
            capacity: 1,
            output_budget: 1,
        },
        Charge::Canonicalize { ids: 1 },
    ] {
        admitted
            .meter
            .charge(WorkScheduleV1::cost(charge).unwrap())
            .unwrap();
    }
    assert_eq!(admitted.meter.used(), WorkUnits(301));
    publication.write(0, DecodeOutcome::Decoded { ids: &[2] }, false);
    let failure = admitted
        .meter
        .charge(WorkScheduleV1::cost(Charge::Compare { capacity: 1 }).unwrap())
        .unwrap_err();
    publication.fail(failure);
    assert_eq!(
        publication
            .finish(admitted.meter.used(), layout.total_bytes())
            .unwrap_err(),
        DecodeError::WorkLimitExceeded,
        "an admitted request loses every row result when a later charge fails"
    );
    for reason in [
        DecodeFailure::DegreeExceedsBudget,
        DecodeFailure::InvalidLocator,
        DecodeFailure::NotSplit,
        DecodeFailure::VerificationFailed,
    ] {
        let mut publication = Publication::new(scratch.split(&layout).1, &layout);
        publication.write(0, DecodeOutcome::Failed { reason }, false);
        publication.write(1, DecodeOutcome::Decoded { ids: &[1] }, false);
        let report = publication
            .finish(WorkUnits(9), layout.total_bytes())
            .unwrap();
        assert_eq!(report.outcome(0), Some(DecodeOutcome::Failed { reason }));
        assert_eq!(
            report.outcome(1),
            Some(DecodeOutcome::Decoded { ids: &[1] })
        );
        assert_eq!(report.peak_scratch_bytes, layout.total_bytes());
    }
    // Dropping unfinished publication releases scratch without publishing stale row 0.
    {
        let mut p = Publication::new(scratch.split(&layout).1, &layout);
        p.write(0, DecodeOutcome::Equal, false);
    }
    let mut p = Publication::new(scratch.split(&layout).1, &layout);
    p.write(0, DecodeOutcome::Equal, false);
    p.write(1, DecodeOutcome::Equal, false);
    assert_eq!(
        p.finish(WorkUnits(0), layout.total_bytes())
            .unwrap()
            .outcome(0),
        Some(DecodeOutcome::Equal)
    );
}

const WORK_CASES: &[(Charge, u64)] = &[
    (Charge::Admission { rows: 2 }, 3),
    (Charge::Normalize { inputs: 0 }, 0),
    (Charge::Normalize { inputs: 1 }, 3),
    (Charge::Normalize { inputs: 2 }, 8),
    (Charge::Normalize { inputs: 5 }, 30),
    (Charge::Compare { capacity: 1 }, 2),
    (Charge::Reconstruct { capacity: 3 }, 9),
    (Charge::BmStep { budget: 2 }, 146),
    (
        Charge::Candidates {
            degree: 2,
            inputs: 5,
        },
        30,
    ),
    (Charge::Deflate { degree: 2 }, 12),
    (Charge::Table { degree: 3 }, 78),
    (Charge::Trace { degree: 3 }, 2205),
    (Charge::SplitCheck { degree: 3 }, 37),
    (Charge::Gcd { degree: 3 }, 640),
    (Charge::Divide { degree: 3 }, 192),
    (Charge::SplitAssembly { degree: 3 }, 16),
    (Charge::Leaf { degree: 0 }, 0),
    (Charge::Leaf { degree: 1 }, 1),
    (Charge::Leaf { degree: 2 }, 160),
    (
        Charge::Verify {
            capacity: 3,
            output_budget: 2,
        },
        24,
    ),
    (Charge::Canonicalize { ids: 5 }, 20),
];

#[test]
fn work_schedule_v1() {
    let cases = WORK_CASES;
    let vectors: Vec<_> = include_str!("../../tests/vectors/work-v1.tsv")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
        .collect();
    assert_eq!(cases.len(), vectors.len());
    for (&(charge, expected), vector) in cases.iter().zip(vectors) {
        assert_eq!(
            vector
                .split_whitespace()
                .last()
                .unwrap()
                .parse::<u64>()
                .unwrap(),
            expected,
            "committed work vector {vector}"
        );
        assert_eq!(
            WorkScheduleV1::cost(charge).unwrap(),
            WorkUnits(expected),
            "{charge:?}"
        );
    }
    for (r, expected) in [(0, 0), (1, 160), (2, 320), (3, 185_214)] {
        assert_eq!(
            WorkScheduleV1::roots_bound(r).unwrap(),
            WorkUnits(expected),
            "root budget {r}"
        );
    }
    for r in 0..=32 {
        let mut operational = 160 * r as u64;
        for degree in 3..=r {
            let cost = |c| WorkScheduleV1::cost(c).unwrap().0;
            operational += cost(Charge::Table { degree })
                + 64 * (cost(Charge::Trace { degree })
                    + cost(Charge::SplitCheck { degree })
                    + cost(Charge::Gcd { degree }))
                + cost(Charge::Divide { degree })
                + cost(Charge::SplitAssembly { degree });
        }
        assert_eq!(
            WorkScheduleV1::roots_bound(r).unwrap(),
            WorkUnits(operational),
            "closed bound equals operational V1 table at budget {r}"
        );
    }
    assert_eq!(
        WorkScheduleV1::cost(Charge::Normalize { inputs: usize::MAX }),
        Err(DecodeError::WorkLimitExceeded)
    );
    let mut m = WorkMeter::new(WorkUnits(3));
    m.charge(WorkUnits(3)).unwrap();
    assert_eq!(m.used(), WorkUnits(3));
    assert_eq!(m.charge(WorkUnits(1)), Err(DecodeError::WorkLimitExceeded));
    assert_eq!(
        m.charge(WorkUnits(0)),
        Err(DecodeError::WorkLimitExceeded),
        "failed charge is terminal even if a later charge is free"
    );
    let mut m = WorkMeter::new(WorkUnits(u64::MAX));
    m.charge(WorkUnits(u64::MAX)).unwrap();
    assert_eq!(
        m.charge(WorkUnits(1)),
        Err(DecodeError::WorkLimitExceeded),
        "overflow never authorizes work"
    );
}

#[test]
fn scratch_segments_are_disjoint() {
    use scratch::RowLayout;
    let row = RowLayout::new(3, 2).unwrap();
    let mut offset = 0;
    let segments = [
        row.difference,
        row.syndromes,
        row.bm,
        row.polynomials,
        row.factors,
        row.square_table,
        row.verification,
        row.roots,
    ]
    .map(|len| {
        let start = offset;
        offset += len;
        start..offset
    });
    assert_eq!(segments[0], 0..3);
    assert_eq!(segments[1], 3..10);
    assert_eq!(segments[2], 10..26);
    assert_eq!(segments[3], 26..50);
    assert_eq!(segments[4], 50..68);
    assert_eq!(segments[5], 68..70);
    assert_eq!(segments[6], 70..73);
    assert_eq!(segments[7], 73..75);
    assert_eq!(row.words, 75);
    assert_eq!(row.raw_products, 8);
    assert_eq!(
        RowLayout::new(usize::MAX, 0).unwrap_err(),
        DecodeError::ScratchTooSmall
    );
    let plan = DecodePlan::v1();
    let layout = ScratchLayout::for_plan(&plan, &[1, 1], &[Some(1), Some(1)], 1, 0).unwrap();
    for segment in 0..5 {
        let mut scratch = DecodeScratch::<Gf64>::new(&layout).unwrap();
        match segment {
            0 => scratch.words.clear(),
            1 => scratch.raw.clear(),
            2 => scratch.factors.clear(),
            3 => scratch.ids.clear(),
            _ => scratch.outcomes.clear(),
        }
        assert!(
            !scratch.covers(&layout),
            "every segment, including metadata/results, is admitted"
        );
    }
    let bytes = record(&[1, 1], false);
    let local = owned(&bytes);
    let remote = SketchView::parse(&bytes, &wire_limits()).unwrap();
    let mut caps = limits(1);
    caps.max_scratch_bytes = layout.total_bytes() - 1;
    let full = DecodeScratch::new(&layout).unwrap();
    macro_rules! req {
        () => {
            DecodeRequest {
                local: &local,
                remote,
                candidates: &[],
                plan: &plan,
                limits: &caps,
            }
        };
    }
    assert_eq!(
        admit(&req!(), &full).unwrap_err(),
        DecodeError::ScratchTooSmall,
        "byte cap applies even when every supplied segment is sufficient"
    );
    caps.max_scratch_bytes = layout.total_bytes();
    assert!(
        admit(&req!(), &full).is_ok(),
        "the exact required byte cap admits the request"
    );
    let bigger = ScratchLayout::for_plan(&plan, &[2, 2], &[Some(2), Some(2)], 2, 0).unwrap();
    let oversized = DecodeScratch::new(&bigger).unwrap();
    assert!(
        admit(&req!(), &oversized).is_ok(),
        "unused reusable capacity does not consume the request scratch cap"
    );
}

#[test]
fn snapshot_import_is_owned() {
    let mut bytes = record(&[1, 1], true);
    bytes[37..45].copy_from_slice(&u64::MAX.to_le_bytes());
    let frozen = owned(&bytes);
    let sibling = frozen.clone();
    bytes.fill(0);
    assert_eq!(
        frozen.state.words,
        &[0, u64::MAX],
        "owned import preserves canonical top-bit words independently of source bytes"
    );
    assert_eq!(frozen.state.zero_words, &[1]);
    assert_eq!(frozen.state.encoded_v1.get().unwrap()[28], 1);
    assert!(
        std::sync::Arc::ptr_eq(&frozen.state, &sibling.state),
        "frozen clone is constant-time sharing"
    );
    assert_eq!(frozen.shape().capacities(), &[1, 1]);
    assert_eq!(frozen.shape().wire_bytes(), 45);
    let source = record(&[1, 1], true);
    let view = SketchView::<Gf64>::parse(&source, &wire_limits()).unwrap();
    let tiny = ShapeLimits {
        max_wire_bytes: 4096,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 1,
    };
    assert_eq!(
        FrozenSketch::from_view(view, &tiny).unwrap_err(),
        crate::ShapeError::InputLimitExceeded,
        "owned adapters admit before allocating"
    );
    send_sync::<FrozenSketch<Gf64>>();
}

mod composition;
