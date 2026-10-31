//! V3 rejection through the real job, including the terminal stage's next Compare.
#![forbid(unsafe_code)]

use {
    super::{DecodeJob, JobState},
    crate::{
        BackendId, BackendRequest, DecodeError, DecodeFailure, DecodeLimits, DecodeOutcome,
        DecodePlan, DecodeRequest, DecodeScratch, Decoder, Gf64, MutableSketch, ParseLimits,
        ShapeLimits, SketchShape, SketchView, Stage, StageProgress, WorkUnits, decode_into,
        field::reference,
    },
    std::sync::Arc,
};

// Four capacity-18 rows, beta=18, two hints. These boundaries include the preceding
// successful row, Admission=5, Normalize=8 and each Compare=19. The residual degree
// is 10 after two real deflations; a quartic prefix coincidence pays 3106 before
// full Verification rejects it and resumes BM. Table=820 and AffinePreparation=26770.
const BEFORE_PREPARATION: u64 = 10831 + 3106;
const AFTER_PREPARATION: u64 = BEFORE_PREPARATION + 26770;
const AFTER_COMPARE: u64 = AFTER_PREPARATION + 19;
const COMPLETE: u64 = AFTER_COMPARE + 1 + 721 + 108 + 19;

fn progress(bucket: usize, stage: Stage, work: u64, peak: usize) -> StageProgress {
    StageProgress::Completed {
        bucket,
        stage,
        work: WorkUnits(work),
        peak_scratch_bytes: peak,
        locator_degree: if bucket == 1
            && !matches!(
                stage,
                Stage::Reconstruction
                    | Stage::GuardThree
                    | Stage::GuardFour
                    | Stage::NewtonFour
                    | Stage::LeafFour
                    | Stage::FactorVerification
                    | Stage::Verification
            ) {
            12
        } else {
            0
        },
        candidate_hits: usize::from(
            bucket == 1
                && matches!(
                    stage,
                    Stage::CandidateEvaluation
                        | Stage::Deflation
                        | Stage::ReducerPreparation
                        | Stage::AffinePreparation
                ),
        ) * 2,
        trace_attempts: 0,
        gcd_degree: 0,
    }
}

fn polynomial(roots: &[u64]) -> Vec<u64> {
    let mut coefficients = vec![1];
    for &root in roots {
        let mut next = vec![0; coefficients.len() + 1];
        for (i, &coefficient) in coefficients.iter().enumerate() {
            next[i] ^= reference::mul::<Gf64>(coefficient, root);
            next[i + 1] ^= coefficient;
        }
        coefficients = next;
    }
    coefficients
}

fn reach_preparation(job: &mut DecodeJob<'_, '_, Gf64>, peak: usize) {
    let original: Vec<_> = (0..12).map(|i| 1 + 4 * i).collect();
    // No public binary-BM reproducer is known. Inject only coefficients AFTER BM;
    // do not set the degree, state, dispatch, roots, meter, or completion outcome.
    // CandidateEvaluation and Deflation really remove 5 and 9, leaving the known
    // repeated degree-10 residual. Public parity inputs cancel duplicate roots.
    let injected = polynomial(&[5, 9, 3, 3, 2, 1, 7, 11, 19, 35, 67, 131]);
    for (bucket, stage, work) in [
        (0, Stage::DirectOne, 33),
        (0, Stage::Verification, 754),
        (0, Stage::Canonicalization, 881),
        (1, Stage::GuardThree, 881 + 48),
        (1, Stage::GuardFour, 881 + 128),
        (1, Stage::NewtonFour, 1169),
        (1, Stage::LeafFour, 3217),
        (1, Stage::FactorVerification, 3266),
        (1, Stage::Verification, 3987),
        (1, Stage::Reconstruction, 935 + 3106),
        (1, Stage::BerlekampMassey, 9647 + 3106),
        (1, Stage::CandidateEvaluation, 9699 + 3106),
        (1, Stage::Deflation, 10011 + 3106),
        (1, Stage::ReducerPreparation, BEFORE_PREPARATION),
    ] {
        assert_eq!(job.next_stage(), Some(stage));
        if stage == Stage::CandidateEvaluation {
            let JobState::Row { layout, .. } = &job.state else {
                panic!("real BM must leave the job in its general row");
            };
            let (_, _, workspace) = job.workspace.row(layout);
            assert_eq!(&workspace.bm[..13], polynomial(&original));
            workspace.bm[..injected.len()].copy_from_slice(&injected);
        }
        assert_eq!(job.run_next(), progress(bucket, stage, work, peak));
    }
    assert_eq!(job.next_stage(), Some(Stage::AffinePreparation));
    let JobState::Row { layout, .. } = &job.state else {
        panic!("real deflation must dispatch affine preparation");
    };
    let (_, _, workspace) = job.workspace.row(layout);
    assert_eq!(
        &workspace.polynomials[..11],
        polynomial(&[3, 3, 2, 1, 7, 11, 19, 35, 67, 131]),
        "real deflation must preserve the repeated residual"
    );
    assert_eq!(&workspace.roots[..2], &[5, 9]);
}

fn assert_exhausted(job: &mut DecodeJob<'_, '_, Gf64>, used: u64) {
    assert_eq!(job.next_stage(), None);
    for _ in 0..2 {
        assert_eq!(
            job.run_next(),
            StageProgress::Failed(DecodeError::WorkLimitExceeded)
        );
        assert_eq!(job.meter.used(), WorkUnits(used));
    }
    assert_eq!(
        job.meter.charge(WorkUnits(0)),
        Err(DecodeError::WorkLimitExceeded)
    );
}

#[test]
fn v3_repeated_factor_rejection_through_decode_job() {
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[18; 4],
            &ShapeLimits {
                max_wire_bytes: 1000,
                max_buckets: 4,
                max_capacity_per_bucket: 18,
                max_total_syndrome_words: 72,
            },
        )
        .unwrap(),
    );
    let local = MutableSketch::new(shape, BackendRequest::Auto)
        .unwrap()
        .freeze();
    let original: Vec<_> = (0..12).map(|i| 1 + 4 * i).collect();
    let mut remote = local.thaw(BackendRequest::Auto).unwrap();
    for id in [4, 2].into_iter().chain(original.iter().copied()) {
        remote.toggle(id);
    }
    let remote = remote.freeze();
    let view = SketchView::parse(
        remote.encoded_v1().unwrap(),
        &ParseLimits {
            max_wire_bytes: 1000,
            max_buckets: 4,
            max_capacity_per_bucket: 18,
            max_total_syndrome_words: 72,
        },
    )
    .unwrap();
    let plan = DecodePlan::v3();
    let (bound, layout) = plan
        .complete_bound(&[18; 4], &[Some(18); 4], 18, 2)
        .unwrap();
    let peak = layout.total_bytes();
    let full_limits = DecodeLimits {
        max_output_per_bucket: 18,
        max_candidate_inputs: 2,
        max_work: bound,
        max_scratch_bytes: peak,
    };
    let full_request = DecodeRequest {
        local: &local,
        remote: view,
        candidates: &[5, 9],
        plan: &plan,
        limits: &full_limits,
    };
    let mut cases = 0;
    for backend in [
        BackendId::Portable,
        BackendId::Pclmul,
        BackendId::Vpclmul512,
    ] {
        let decoder = match Decoder::new(BackendRequest::Force(backend), 1) {
            Ok(decoder) => decoder,
            Err(_) if backend != BackendId::Portable => continue,
            Err(error) => panic!("portable decoder must be available: {error:?}"),
        };
        let mut scratch = DecodeScratch::new(&layout).unwrap();
        for limit in [
            AFTER_PREPARATION - 1,
            AFTER_PREPARATION,
            AFTER_PREPARATION + 1,
            AFTER_COMPARE - 1,
            AFTER_COMPARE,
            AFTER_COMPARE + 1,
            COMPLETE - 1,
            COMPLETE,
            COMPLETE + 1,
            bound.0,
        ] {
            let limits = DecodeLimits {
                max_work: WorkUnits(limit),
                ..full_limits
            };
            let mut job = DecodeJob::new(
                DecodeRequest {
                    limits: &limits,
                    ..full_request
                },
                &decoder,
                &mut scratch,
            )
            .unwrap();
            reach_preparation(&mut job, peak);
            let rejection = job.run_next();
            if limit < AFTER_COMPARE {
                assert_eq!(
                    rejection,
                    StageProgress::Failed(DecodeError::WorkLimitExceeded),
                    "preparation and following Compare precede public rejection progress"
                );
                let prepared = limit >= AFTER_PREPARATION;
                assert_eq!(job.bucket, if prepared { 2 } else { 1 });
                assert_exhausted(
                    &mut job,
                    if prepared {
                        AFTER_PREPARATION
                    } else {
                        BEFORE_PREPARATION
                    },
                );
                assert_eq!(
                    job.finish().map(|_| ()),
                    Err(DecodeError::WorkLimitExceeded),
                    "earlier successful rows must not escape a failed request"
                );
            } else {
                assert_eq!(
                    rejection,
                    progress(1, Stage::AffinePreparation, AFTER_COMPARE, peak),
                    "repeated locator must terminate through the job at charged preparation"
                );
                assert_eq!(
                    job.bucket, 2,
                    "rejection advances to the successful neighbor"
                );
                assert_eq!(job.next_stage(), Some(Stage::DirectOne));
                let mut used = AFTER_COMPARE;
                for (stage, work, charged_before_compare) in [
                    (Stage::DirectOne, AFTER_COMPARE + 1, AFTER_COMPARE + 1),
                    (
                        Stage::Verification,
                        AFTER_COMPARE + 722,
                        AFTER_COMPARE + 722,
                    ),
                    (Stage::Canonicalization, COMPLETE, COMPLETE - 19),
                ] {
                    assert_eq!(job.next_stage(), Some(stage));
                    let observed = job.run_next();
                    if limit < work {
                        assert_eq!(
                            observed,
                            StageProgress::Failed(DecodeError::WorkLimitExceeded)
                        );
                        if limit >= charged_before_compare {
                            used = charged_before_compare;
                        }
                        assert_exhausted(&mut job, used);
                        break;
                    }
                    assert_eq!(observed, progress(2, stage, work, peak));
                    used = work;
                }
                if limit < COMPLETE {
                    assert_eq!(
                        job.finish().map(|_| ()),
                        Err(DecodeError::WorkLimitExceeded),
                        "a completed NotSplit row is private until the whole request finishes"
                    );
                } else {
                    assert_eq!(job.next_stage(), None);
                    let report = job.finish().unwrap();
                    assert_eq!(report.work, WorkUnits(COMPLETE));
                    assert_eq!(report.peak_scratch_bytes, peak);
                    assert_eq!(
                        report.outcome(0),
                        Some(DecodeOutcome::Decoded { ids: &[4] })
                    );
                    assert_eq!(
                        report.outcome(1),
                        Some(DecodeOutcome::Failed {
                            reason: DecodeFailure::NotSplit
                        })
                    );
                    assert_eq!(
                        report.outcome(2),
                        Some(DecodeOutcome::Decoded { ids: &[2] })
                    );
                    assert_eq!(report.outcome(3), Some(DecodeOutcome::Equal));
                    assert_eq!(
                        report.result_offsets(),
                        vec![(0, 1), (0, 0), (1, 1), (0, 0)],
                        "neither injected roots nor candidate hits are published for NotSplit"
                    );
                }
            }
            cases += 1;
        }
        // Dropping before rejection, after rejection, or after all stages lends no
        // report. The arena must be reusable without leaking the injected outcome.
        for stop in 0..3 {
            {
                let mut job = DecodeJob::new(full_request, &decoder, &mut scratch).unwrap();
                reach_preparation(&mut job, peak);
                if stop >= 1 {
                    assert_eq!(
                        job.run_next(),
                        progress(1, Stage::AffinePreparation, AFTER_COMPARE, peak)
                    );
                }
                if stop == 2 {
                    while job.next_stage().is_some() {
                        assert!(matches!(job.run_next(), StageProgress::Completed { .. }));
                    }
                }
            }
            let report = decode_into(full_request, &decoder, &mut scratch).unwrap();
            assert_eq!(
                report.outcome(0),
                Some(DecodeOutcome::Decoded { ids: &[4] })
            );
            assert_eq!(
                report.outcome(1),
                Some(DecodeOutcome::Decoded { ids: &original })
            );
            assert_eq!(
                report.outcome(2),
                Some(DecodeOutcome::Decoded { ids: &[2] })
            );
            assert_eq!(report.outcome(3), Some(DecodeOutcome::Equal));
        }
    }
    println!(
        "V3_JOB_REPEATED_REJECTION cases={cases} preparation={AFTER_PREPARATION} \
         following_compare={AFTER_COMPARE} complete={COMPLETE}"
    );
}
