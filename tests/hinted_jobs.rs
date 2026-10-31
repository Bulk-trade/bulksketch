//! Production V3 job: zero-channel tiny row followed by a hinted general row.
#![forbid(unsafe_code)]
use {bulksketch::*, std::sync::Arc};

#[test]
fn candidates_preserve_prefix_and_zero_channel() {
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[89; 2],
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 2,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 178,
            },
        )
        .unwrap(),
    );
    let local = MutableSketch::new(shape, BackendRequest::Auto).unwrap();
    let mut remote = local.clone();
    let expected = [vec![0, 2], vec![3, 7, 11, 19, 35]];
    for &id in expected.iter().flatten() {
        remote.toggle(id);
    }
    let local = local.freeze();
    let remote = remote.freeze();
    let view = SketchView::parse(
        remote.encoded_v1().unwrap(),
        &ParseLimits {
            max_wire_bytes: 100_000,
            max_buckets: 2,
            max_capacity_per_bucket: 89,
            max_total_syndrome_words: 178,
        },
    )
    .unwrap();
    let plan = DecodePlan::v3();
    let mut checked = 0;
    for backend in [
        BackendId::Portable,
        BackendId::Pclmul,
        BackendId::Vpclmul512,
    ] {
        let Ok(decoder) = Decoder::new(BackendRequest::Force(backend), 0x55) else {
            continue;
        };
        // The partial case leaves residual d3, exercising certified recovery after
        // deflation. Every case verifies the complete d5 answer through LFSR.
        for (candidates, hits, affine, leaf) in [
            (vec![0, 999], 0, true, false),
            (vec![0, 3, 3, 7, 999], 2, false, true),
            (vec![0, 3, 7, 11, 19, 35, 999], 5, false, false),
        ] {
            let (bound, layout) = plan
                .complete_bound(&[89; 2], &[Some(88), Some(89)], 89, candidates.len())
                .unwrap();
            let limits = DecodeLimits {
                max_output_per_bucket: 89,
                max_candidate_inputs: candidates.len(),
                max_work: bound,
                max_scratch_bytes: layout.total_bytes(),
            };
            let mut scratch = DecodeScratch::new(&layout).unwrap();
            let mut job = DecodeJob::new(
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
            let mut observed_hits = 0;
            let mut saw_affine = false;
            let mut saw_leaf = false;
            while job.next_stage().is_some() {
                match job.run_next() {
                    StageProgress::Completed {
                        bucket: 1,
                        stage,
                        candidate_hits,
                        ..
                    } => {
                        observed_hits = observed_hits.max(candidate_hits);
                        saw_affine |= stage == Stage::AffinePreparation;
                        saw_leaf |= stage == Stage::LeafThree;
                    }
                    StageProgress::Completed { .. } => {}
                    StageProgress::Failed(e) => panic!("hinted V3 job failed: {e:?}"),
                }
            }
            let report = job.finish().unwrap();
            assert_eq!(observed_hits, hits, "normalized candidate hits");
            assert_eq!(saw_affine, affine, "residual-degree affine dispatch");
            assert_eq!(saw_leaf, leaf, "residual-degree closed-form dispatch");
            for (bucket, ids) in expected.iter().enumerate() {
                assert_eq!(
                    report.outcome(bucket),
                    Some(DecodeOutcome::Decoded { ids }),
                    "V3 hinted roots and zero channel backend={backend:?} hits={hits} \
                     bucket={bucket}"
                );
            }
            checked += 1;
        }
    }
    assert!(checked >= 2, "portable backend must execute both cases");
    println!("ROOTMIX_CANDIDATE_ZERO_CASES {checked}");
}
