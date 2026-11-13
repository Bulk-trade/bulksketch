//! Rows passed as raw syndrome bytes (`decode_rows_into`) decode like parsed
//! sketches: same results, same work, same failure behaviour.
use {
    bulksketch::{
        BackendRequest, DecodeError, DecodeLimits, DecodeOutcome, DecodePlan, DecodeRequest,
        DecodeRow, DecodeRowsRequest, DecodeScratch, Decoder, FrozenSketch, Gf64, MutableSketch,
        ParseLimits, ShapeLimits, SketchShape, SketchView, WorkUnits, decode_into,
        decode_rows_into,
    },
    std::sync::Arc,
};

const CAPACITY: usize = 18;

fn sketch(ids: &[u64]) -> FrozenSketch<Gf64> {
    let shape = SketchShape::new(
        &[CAPACITY],
        &ShapeLimits {
            max_wire_bytes: 1024,
            max_buckets: 1,
            max_capacity_per_bucket: CAPACITY,
            max_total_syndrome_words: CAPACITY,
        },
    )
    .unwrap();
    let mut sketch = MutableSketch::new(Arc::new(shape), BackendRequest::Auto).unwrap();
    for &id in ids {
        sketch.toggle(id);
    }
    sketch.freeze()
}

fn limits(rows: usize, candidates: usize) -> (DecodeLimits, DecodeScratch<Gf64>) {
    let (max_work, layout) = DecodePlan::v2()
        .complete_bound(
            &vec![CAPACITY as u16; rows],
            &vec![Some(CAPACITY); rows],
            CAPACITY,
            candidates,
        )
        .unwrap();
    (
        DecodeLimits {
            max_output_per_bucket: CAPACITY,
            max_candidate_inputs: candidates,
            max_work,
            max_scratch_bytes: layout.total_bytes(),
        },
        DecodeScratch::new(&layout).unwrap(),
    )
}

fn payload(sketch: &FrozenSketch<Gf64>) -> &[u8] {
    &sketch.encoded_v1().unwrap()[27..]
}

#[test]
fn borrowed_unaligned_row_matches_canonical_result_and_work() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 123).unwrap();
    for count in [0, 1, 2, 5, 18, 19] {
        for zero in [false, true] {
            let local = sketch(if zero { &[0, 40] } else { &[40] });
            let remote = sketch(&(1..=count).chain([40]).collect::<Vec<_>>());
            // Offset one deliberately prevents an aligned-u64 payload assumption.
            let mut unaligned = vec![0];
            unaligned.extend_from_slice(payload(&remote));
            let candidates = [0, 1, 1, 2, 7, u64::MAX];
            let (limits, mut canonical_scratch) = limits(1, candidates.len());
            let (_, mut borrowed_scratch) = self::limits(1, candidates.len());
            let view = SketchView::parse(
                remote.encoded_v1().unwrap(),
                &ParseLimits {
                    max_wire_bytes: 1024,
                    max_buckets: 1,
                    max_capacity_per_bucket: CAPACITY,
                    max_total_syndrome_words: CAPACITY,
                },
            )
            .unwrap();
            let expected = decode_into(
                DecodeRequest {
                    local: &local,
                    remote: view,
                    candidates: &candidates,
                    plan: &plan,
                    limits: &limits,
                },
                &decoder,
                &mut canonical_scratch,
            )
            .unwrap();
            let rows = [DecodeRow {
                local: &local,
                remote: &unaligned[1..],
                candidates: &candidates,
            }];
            let actual = decode_rows_into(
                DecodeRowsRequest {
                    rows: &rows,
                    plan: &plan,
                    limits: &limits,
                },
                &decoder,
                &mut borrowed_scratch,
            )
            .unwrap();
            assert_eq!(
                actual.outcome(0),
                expected.outcome(0),
                "count={count},zero={zero}"
            );
            assert_eq!(actual.work, expected.work);
            assert_eq!(actual.peak_scratch_bytes, expected.peak_scratch_bytes);
        }
    }
}

#[test]
fn borrowed_batch_preserves_independent_candidates_and_partial_failure() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 123).unwrap();
    let local = sketch(&[]);
    let first = sketch(&[1, 2, 3, 4, 5]);
    let overflow = sketch(&(1..=19).collect::<Vec<_>>());
    let last = sketch(&[1, 2, 3, 4, 6]);
    // Same hints in different rows must not be globally deduplicated or rerouted.
    let candidates = [0, 1, 1, 2, 3, 4, 5, 6];
    let rows = [
        DecodeRow {
            local: &local,
            remote: payload(&first),
            candidates: &candidates,
        },
        DecodeRow {
            local: &local,
            remote: payload(&overflow),
            candidates: &candidates,
        },
        DecodeRow {
            local: &local,
            remote: payload(&last),
            candidates: &candidates,
        },
    ];
    let (limits, mut scratch) = limits(3, 3 * candidates.len());
    let report = decode_rows_into(
        DecodeRowsRequest {
            rows: &rows,
            plan: &plan,
            limits: &limits,
        },
        &decoder,
        &mut scratch,
    )
    .unwrap();
    assert_eq!(
        report.bucket_count(),
        3,
        "non-power-of-two independent batch"
    );
    assert_eq!(
        report.outcome(0),
        Some(DecodeOutcome::Decoded {
            ids: &[1, 2, 3, 4, 5]
        })
    );
    assert!(matches!(
        report.outcome(1),
        Some(DecodeOutcome::Failed { .. })
    ));
    assert_eq!(
        report.outcome(2),
        Some(DecodeOutcome::Decoded {
            ids: &[1, 2, 3, 4, 6]
        })
    );
    let mut independent_work = 0;
    for (bucket, remote) in [&first, &overflow, &last].into_iter().enumerate() {
        let (limits, mut scratch) = self::limits(1, candidates.len());
        let view = SketchView::parse(
            remote.encoded_v1().unwrap(),
            &ParseLimits {
                max_wire_bytes: 1024,
                max_buckets: 1,
                max_capacity_per_bucket: CAPACITY,
                max_total_syndrome_words: CAPACITY,
            },
        )
        .unwrap();
        let expected = decode_into(
            DecodeRequest {
                local: &local,
                remote: view,
                candidates: &candidates,
                plan: &plan,
                limits: &limits,
            },
            &decoder,
            &mut scratch,
        )
        .unwrap();
        assert_eq!(report.outcome(bucket), expected.outcome(0));
        independent_work += expected.work.0;
    }
    // V2 Admission: 1 + rows; Normalize: n * (ceil(log2(n)) + 3).
    // Three requests use 6 + 3*48; the batch uses 4 + 192.
    assert_eq!(
        report.work.0,
        independent_work + 46,
        "row-local hints retain their charged work"
    );
}

#[test]
fn borrowed_shape_admission_precedes_plan_work_and_scratch() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 123).unwrap();
    let local = sketch(&[]);
    let (mut limits, mut scratch) = limits(1, 0);
    limits.max_output_per_bucket = CAPACITY + 1;
    limits.max_work = WorkUnits(0);
    limits.max_scratch_bytes = 0;
    for len in [0, 1, CAPACITY * 8 - 1, CAPACITY * 8 + 1] {
        let bytes = vec![0; len];
        let rows = [DecodeRow {
            local: &local,
            remote: &bytes,
            candidates: &[],
        }];
        let error = decode_rows_into(
            DecodeRowsRequest {
                rows: &rows,
                plan: &plan,
                limits: &limits,
            },
            &decoder,
            &mut scratch,
        )
        .unwrap_err();
        assert_eq!(error, DecodeError::ShapeMismatch, "length={len}");
    }
    assert_eq!(
        decode_rows_into(
            DecodeRowsRequest {
                rows: &[],
                plan: &plan,
                limits: &limits
            },
            &decoder,
            &mut scratch
        )
        .unwrap_err(),
        DecodeError::ShapeMismatch
    );
}

#[test]
fn borrowed_work_failure_does_not_publish_earlier_rows_and_arena_is_reusable() {
    let plan = DecodePlan::v2();
    let decoder = Decoder::new(BackendRequest::Auto, 123).unwrap();
    let local = sketch(&[]);
    let remote = sketch(&[1]);
    let rows = [
        DecodeRow {
            local: &local,
            remote: payload(&remote),
            candidates: &[],
        },
        DecodeRow {
            local: &local,
            remote: payload(&remote),
            candidates: &[],
        },
    ];
    let (limits, mut scratch) = limits(2, 0);
    let (one_limits, mut one_scratch) = self::limits(1, 0);
    let first_work = decode_rows_into(
        DecodeRowsRequest {
            rows: &rows[..1],
            plan: &plan,
            limits: &one_limits,
        },
        &decoder,
        &mut one_scratch,
    )
    .unwrap()
    .work
    .0;
    // Batch admission adds one unit: first decoded row completes, then the
    // second Compare fails inside the staged advance, after private publication.
    let tight = DecodeLimits {
        max_work: WorkUnits(first_work + 1),
        ..limits
    };
    assert_eq!(
        decode_rows_into(
            DecodeRowsRequest {
                rows: &rows,
                plan: &plan,
                limits: &tight
            },
            &decoder,
            &mut scratch
        )
        .unwrap_err(),
        DecodeError::WorkLimitExceeded
    );
    let report = decode_rows_into(
        DecodeRowsRequest {
            rows: &rows,
            plan: &plan,
            limits: &limits,
        },
        &decoder,
        &mut scratch,
    )
    .unwrap();
    assert_eq!(
        report.outcome(0),
        Some(DecodeOutcome::Decoded { ids: &[1] })
    );
    assert_eq!(
        report.outcome(1),
        Some(DecodeOutcome::Decoded { ids: &[1] })
    );
}
