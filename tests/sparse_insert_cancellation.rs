#![forbid(unsafe_code)]

use {
    bulksketch::{
        BackendId, BackendRequest, Gf64, InsertScratch, MutableSketch, ParseLimits, ShapeLimits,
        SketchShape, SketchView,
    },
    std::sync::Arc,
};

fn check_sparse_cancellation(ids: &[u64]) {
    assert_eq!(ids.iter().fold(0, |sum, id| sum ^ id), 0);
    for (index, id) in ids.iter().enumerate() {
        assert_ne!(*id, 0);
        assert!(!ids[..index].contains(id), "IDs must be distinct");
    }
    let limits = ParseLimits {
        max_wire_bytes: 100_000,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 1424,
    };
    for capacity in [18, 72, 89] {
        let shape = Arc::new(
            SketchShape::<Gf64>::new(
                &[capacity; 16],
                &ShapeLimits {
                    max_wire_bytes: limits.max_wire_bytes,
                    max_buckets: limits.max_buckets,
                    max_capacity_per_bucket: limits.max_capacity_per_bucket,
                    max_total_syndrome_words: limits.max_total_syndrome_words,
                },
            )
            .unwrap(),
        );
        assert!(ids.iter().all(|&id| shape.bucket_for(id) == 0));
        for initial in [&[][..], &[0, 80, 1, u64::MAX][..]] {
            for reverse in [false, true] {
                let Ok(mut actual) = MutableSketch::new(
                    Arc::clone(&shape),
                    BackendRequest::Force(BackendId::Vpclmul512),
                ) else {
                    return;
                };
                let mut vector_single = actual.clone();
                let mut portable_batch = MutableSketch::new(
                    Arc::clone(&shape),
                    BackendRequest::Force(BackendId::Portable),
                )
                .unwrap();
                let mut portable_single = portable_batch.clone();
                for sketch in [
                    &mut actual,
                    &mut vector_single,
                    &mut portable_batch,
                    &mut portable_single,
                ] {
                    for &id in initial {
                        sketch.toggle(id);
                    }
                }
                let before = portable_single.freeze().encoded_v1().unwrap().to_vec();
                let before_view = SketchView::<Gf64>::parse(&before, &limits).unwrap();
                let mut batch = ids.to_vec();
                if reverse {
                    batch.reverse();
                }
                let mut scratch = InsertScratch::new(ids.len(), 16).unwrap();
                // Public routing sends three/four distinct IDs to bucket zero,
                // so these capacities enter insert_sparse with S1 cancelling.
                for repetition in 1..=2 {
                    actual.toggle_batch(&batch, &mut scratch).unwrap();
                    portable_batch.toggle_batch(ids, &mut scratch).unwrap();
                    for &id in ids {
                        vector_single.toggle(id);
                        portable_single.toggle(id);
                    }
                    let expected = portable_single.freeze();
                    let expected_bytes = expected.encoded_v1().unwrap();
                    let expected_view = SketchView::<Gf64>::parse(expected_bytes, &limits).unwrap();
                    assert_eq!(
                        expected_view.odd_syndrome(0, 0),
                        before_view.odd_syndrome(0, 0),
                        "first syndrome must cancel"
                    );
                    if repetition == 1 {
                        assert!(
                            (1..capacity).any(|word| {
                                expected_view.odd_syndrome(0, word)
                                    != before_view.odd_syndrome(0, word)
                            }),
                            "higher syndromes must change"
                        );
                    } else {
                        assert_eq!(expected_bytes, before, "repeated batch must cancel");
                    }
                    for (name, sketch) in [
                        ("vector batch", &actual),
                        ("vector single", &vector_single),
                        ("portable batch", &portable_batch),
                    ] {
                        let frozen = sketch.freeze();
                        let bytes = frozen.encoded_v1().unwrap();
                        let view = SketchView::<Gf64>::parse(bytes, &limits).unwrap();
                        for bucket in 0..16 {
                            for word in 0..capacity {
                                assert_eq!(
                                    view.odd_syndrome(bucket, word),
                                    expected_view.odd_syndrome(bucket, word),
                                    "{name} c={capacity} n={} reverse={reverse} \
                                     repetition={repetition} initial={initial:?} bucket={bucket} \
                                     word={word}",
                                    ids.len()
                                );
                            }
                        }
                        assert_eq!(bytes, expected_bytes, "{name} complete encoding");
                    }
                }
            }
        }
    }
}

#[test]
fn sparse_three_distinct_ids_cancel_first_syndrome() {
    check_sparse_cancellation(&[16, 32, 48]);
}

#[test]
fn sparse_four_distinct_ids_cancel_first_syndrome() {
    check_sparse_cancellation(&[16, 32, 64, 112]);
}
