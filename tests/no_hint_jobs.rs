//! Plan V3 requests without candidate hints and with a caller-chosen splitter
//! seed: a small row decodes first, then a row takes the general path. The exact
//! work charged is checked.
#![forbid(unsafe_code)]
use {bulksketch::*, std::sync::Arc};

fn fixture(c: usize, d: usize) -> (FrozenSketch<Gf64>, FrozenSketch<Gf64>, Vec<Vec<u64>>) {
    let shape = Arc::new(
        SketchShape::new(
            &[c; 2],
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap(),
    );
    let local = MutableSketch::new(shape, BackendRequest::Auto).unwrap();
    let mut remote = local.clone();
    let rows = vec![
        vec![2],
        (0..d)
            .map(|i| 0x1234_5678_0000_0001 ^ (2 * (i as u64 + 1)))
            .collect(),
    ];
    for &id in rows.iter().flatten() {
        remote.toggle(id);
    }
    (local.freeze(), remote.freeze(), rows)
}

#[test]
fn public_job_dispatch_and_every_integer_work() {
    let mut swept = 0u64;
    for (c, d) in [(18, 3), (18, 5), (89, 5)] {
        let (local, remote, rows) = fixture(c, d);
        let parse = ParseLimits {
            max_wire_bytes: 100_000,
            max_buckets: 16,
            max_capacity_per_bucket: 89,
            max_total_syndrome_words: 1424,
        };
        let view = SketchView::parse(remote.encoded_v1().unwrap(), &parse).unwrap();
        let plan = DecodePlan::v3();
        let (bound, layout) = plan
            .complete_bound(&[c as u16; 2], &[Some(c); 2], c, 0)
            .unwrap();
        let decoder = Decoder::new(BackendRequest::Auto, 0xd6e8_feb8_6659_fd93).unwrap();
        let mut limits = DecodeLimits {
            max_output_per_bucket: c,
            max_candidate_inputs: 0,
            max_work: bound,
            max_scratch_bytes: layout.total_bytes(),
        };
        let mut scratch = DecodeScratch::new(&layout).unwrap();
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
            match job.run_next() {
                StageProgress::Completed { bucket, stage, .. } => {
                    stages.push((bucket, format!("{stage:?}")))
                }
                StageProgress::Failed(e) => panic!("complete bound failed: {e:?}"),
            }
        }
        let report = job.finish().unwrap();
        for (b, expected) in rows.iter().enumerate() {
            assert_eq!(
                report.outcome(b),
                Some(DecodeOutcome::Decoded { ids: expected }),
                "public IDs"
            );
        }
        let used = report.work.0;
        let expected_stage = if d == 3 {
            "LeafThree"
        } else {
            "AffinePreparation"
        };
        assert!(
            stages.iter().any(|(b, s)| *b == 1 && s == expected_stage),
            "V3 row must execute charged dispatch c={c} d={d}: {stages:?}"
        );
        if d == 3 {
            assert!(
                !stages
                    .iter()
                    .any(|(b, s)| *b == 1 && s == "BerlekampMassey")
            );
        }
        assert_eq!(
            stages
                .iter()
                .filter(|(b, _)| *b == 0)
                .map(|(_, s)| s.as_str())
                .collect::<Vec<_>>(),
            ["DirectOne", "Verification", "Canonicalization"],
            "tiny row schedule remains V2"
        );
        for limit in 0..=used {
            limits.max_work = WorkUnits(limit);
            let result = decode_into(
                DecodeRequest {
                    local: &local,
                    remote: view,
                    candidates: &[],
                    plan: &plan,
                    limits: &limits,
                },
                &decoder,
                &mut scratch,
            );
            if limit < used {
                assert!(
                    matches!(result, Err(DecodeError::WorkLimitExceeded)),
                    "all integer limits below completed work reject atomically c={c} d={d} \
                     limit={limit} used={used}"
                );
            } else {
                let r = result.unwrap();
                assert_eq!(r.work.0, used, "exact final work boundary");
                for (b, expected) in rows.iter().enumerate() {
                    assert_eq!(
                        r.outcome(b),
                        Some(DecodeOutcome::Decoded { ids: expected }),
                        "transactional completed IDs"
                    );
                }
            }
            swept += 1;
        }
        println!(
            "ROOTMIX_SWEEP c={c} d={d} limits={} bound={} used={used}",
            used + 1,
            bound.0
        );
    }
    println!("ROOTMIX_EVERY_INTEGER_LIMITS {swept}");
}
