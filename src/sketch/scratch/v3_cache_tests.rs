//! Real V3 no-hint jobs must reuse admission dimensions without changing work.
#![forbid(unsafe_code)]
use {
    super::*,
    crate::{
        field::Gf64,
        sketch::{
            DecodeJob, DecodeLimits, DecodeOutcome, DecodeRequest, Decoder, MutableSketch,
            ParseLimits, ShapeLimits, SketchView, decode_into,
        },
        types::{BackendRequest, WorkUnits},
    },
};

#[test]
fn v3_no_hint_jobs_cache_admission_and_preserve_tight_work() {
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[18; 2],
            &ShapeLimits {
                max_wire_bytes: 1000,
                max_buckets: 2,
                max_capacity_per_bucket: 18,
                max_total_syndrome_words: 36,
            },
        )
        .unwrap(),
    );
    let local = MutableSketch::new(Arc::clone(&shape), BackendRequest::Auto)
        .unwrap()
        .freeze();
    let mut remote = local.thaw(BackendRequest::Auto).unwrap();
    for id in [2, 1, 3, 5, 7, 9] {
        remote.toggle(id);
    }
    let remote = remote.freeze();
    let view = SketchView::parse(
        remote.encoded_v1().unwrap(),
        &ParseLimits {
            max_wire_bytes: 1000,
            max_buckets: 2,
            max_capacity_per_bucket: 18,
            max_total_syndrome_words: 36,
        },
    )
    .unwrap();
    let plan = DecodePlan::v3();
    let (bound, layout) = plan
        .complete_bound(&[18; 2], &[Some(18); 2], 18, 0)
        .unwrap();
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let mut limits = DecodeLimits {
        max_output_per_bucket: 18,
        max_candidate_inputs: 0,
        max_work: bound,
        max_scratch_bytes: layout.total_bytes(),
    };
    let mut scratch = DecodeScratch::new(&layout).unwrap();
    let mut previous = None;
    let mut used = WorkUnits(0);
    for _ in 0..2 {
        let mut job = DecodeJob::new(
            DecodeRequest {
                local: &local,
                remote: view,
                candidates: &[],
                plan: &plan,
                limits: &limits,
            },
            &decoder,
            &mut scratch,
        )
        .unwrap();
        let mut stages = Vec::new();
        while job.next_stage().is_some() {
            stages.push(job.run_next());
        }
        let report = job.finish().unwrap();
        assert_eq!(
            report.outcome(0),
            Some(DecodeOutcome::Decoded { ids: &[2] })
        );
        assert_eq!(
            report.outcome(1),
            Some(DecodeOutcome::Decoded {
                ids: &[1, 3, 5, 7, 9]
            })
        );
        used = report.work;
        if let Some(previous) = &previous {
            assert_eq!(
                &stages, previous,
                "cached admission changed the charged job transcript"
            );
        }
        previous = Some(stages);
        assert!(
            scratch.no_hint_layout.get().is_some(),
            "V3 no-hint job did not cache admission dimensions"
        );
        limits.max_work = used;
    }
    limits.max_work = WorkUnits(used.0 - 1);
    assert!(
        matches!(
            decode_into(
                DecodeRequest {
                    local: &local,
                    remote: view,
                    candidates: &[],
                    plan: &plan,
                    limits: &limits
                },
                &decoder,
                &mut scratch,
            ),
            Err(DecodeError::WorkLimitExceeded)
        ),
        "warm V3 admission bypassed a tight work limit"
    );
    for selected in [DecodePlan::v2(), DecodePlan::v3()] {
        assert_eq!(
            scratch
                .no_hint_layout(&shape, shape.bucket_count(), selected)
                .is_some(),
            selected == plan,
            "cached work-bound proof belongs to a different plan"
        );
        limits.max_work = selected
            .complete_bound(&[18; 2], &[Some(18); 2], 18, 0)
            .unwrap()
            .0;
        let report = decode_into(
            DecodeRequest {
                local: &local,
                remote: view,
                candidates: &[],
                plan: &selected,
                limits: &limits,
            },
            &decoder,
            &mut scratch,
        )
        .unwrap();
        assert_eq!(
            report.outcome(1),
            Some(DecodeOutcome::Decoded {
                ids: &[1, 3, 5, 7, 9]
            })
        );
    }
    limits.max_scratch_bytes = 0;
    for (work, expected) in [
        (WorkUnits(0), DecodeError::WorkLimitExceeded),
        (bound, DecodeError::ScratchTooSmall),
    ] {
        limits.max_work = work;
        assert_eq!(
            DecodeJob::new(
                DecodeRequest {
                    local: &local,
                    remote: view,
                    candidates: &[],
                    plan: &plan,
                    limits: &limits
                },
                &decoder,
                &mut scratch,
            )
            .map(|_| ()),
            Err(expected),
            "warm V3 admission changed work-before-scratch precedence"
        );
    }
}
