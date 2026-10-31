//! Degree-3 and degree-4 rows decoded by the closed-form path (plan V3), checked against both
//! minisketch implementations.
#![forbid(unsafe_code)]
use {bulksketch::*, minisketch_rs::Minisketch, std::sync::Arc};
fn mix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}
#[test]
fn small_degree_rows_match_minisketch() {
    let mut cases = 0;
    for c in [3, 4, 5, 6, 18, 89] {
        for degree in [3, 4, 7, 8] {
            if degree > c {
                continue;
            }
            for sample in 0..64 {
                let mut ids: Vec<_> = (0..degree)
                    .map(|i| mix((sample * 100 + i + 1) as u64))
                    .collect();
                ids.sort_unstable();
                assert!(!ids.contains(&0));
                assert!(ids.windows(2).all(|p| p[0] != p[1]));
                let shape = Arc::new(
                    SketchShape::<Gf64>::new(
                        &[c],
                        &ShapeLimits {
                            max_wire_bytes: 10000,
                            max_buckets: 1,
                            max_capacity_per_bucket: 89,
                            max_total_syndrome_words: 89,
                        },
                    )
                    .unwrap(),
                );
                let local = MutableSketch::new(shape, BackendRequest::Auto)
                    .unwrap()
                    .freeze();
                let mut remote = local.thaw(BackendRequest::Auto).unwrap();
                for &id in &ids {
                    remote.toggle(id);
                }
                let remote = remote.freeze();
                let view = SketchView::parse(
                    remote.encoded_v1().unwrap(),
                    &ParseLimits {
                        max_wire_bytes: 10000,
                        max_buckets: 1,
                        max_capacity_per_bucket: 89,
                        max_total_syndrome_words: 89,
                    },
                )
                .unwrap();
                let hints = if degree > 4 { &ids[..4] } else { &[] };
                let plan = DecodePlan::v3();
                let (bound, layout) = plan
                    .complete_bound(&[u16::try_from(c).unwrap()], &[Some(c)], c, hints.len())
                    .unwrap();
                let limits = DecodeLimits {
                    max_output_per_bucket: c,
                    max_candidate_inputs: hints.len(),
                    max_work: bound,
                    max_scratch_bytes: layout.total_bytes(),
                };
                let decoder = Decoder::new(BackendRequest::Auto, 0xd6e8_feb8_6659_fd93).unwrap();
                let mut scratch = DecodeScratch::new(&layout).unwrap();
                let mut job = DecodeJob::new(
                    DecodeRequest {
                        local: &local,
                        remote: view,
                        candidates: hints,
                        plan: &plan,
                        limits: &limits,
                    },
                    &decoder,
                    &mut scratch,
                )
                .unwrap();
                let mut leaf = false;
                let mut bm = false;
                let mut certificate = false;
                while job.next_stage().is_some() {
                    match job.run_next() {
                        StageProgress::Completed { stage, .. } => {
                            leaf |= matches!(stage, Stage::LeafThree | Stage::LeafFour);
                            bm |= stage == Stage::BerlekampMassey;
                            certificate |= stage == Stage::FactorVerification;
                        }
                        StageProgress::Failed(e) => panic!("complete V3 failed: {e:?}"),
                    }
                }
                let result = job.finish().unwrap();
                assert_eq!(
                    result.outcome(0),
                    Some(DecodeOutcome::Decoded { ids: &ids })
                );
                assert!(
                    leaf && certificate,
                    "actual closed-form production path and certificate must run"
                );
                assert_eq!(bm, degree > 4);
                for implementation in [0, 1] {
                    let Ok(mut oracle) = Minisketch::try_new(64, implementation, c) else {
                        assert_eq!(implementation, 1);
                        continue;
                    };
                    for &id in &ids {
                        oracle.add(id);
                    }
                    let mut decoded = vec![0; c];
                    let len = oracle.decode(&mut decoded).unwrap();
                    decoded.truncate(len);
                    decoded.sort_unstable();
                    assert_eq!(decoded, ids);
                    cases += 1;
                }
            }
        }
    }
    println!("small-degree minisketch cases: {cases}");
}
