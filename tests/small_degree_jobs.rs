//! Explicit V3 public jobs, including zero-S1 whole-row probes and atomic limits.
#![forbid(unsafe_code)]
use {bulksketch::*, std::sync::Arc};

type RunResult = (Vec<u64>, Vec<(String, u64)>, u64);

fn run(
    c: usize,
    beta: usize,
    ids: &[u64],
    plan: DecodePlan,
    limit: Option<u64>,
) -> Result<RunResult, DecodeError> {
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
    for &id in ids {
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
    let zero = usize::from(ids.contains(&0));
    let (bound, layout) = plan.complete_bound(
        &[u16::try_from(c).unwrap()],
        &[beta.checked_sub(zero)],
        beta,
        0,
    )?;
    let limits = DecodeLimits {
        max_output_per_bucket: beta,
        max_candidate_inputs: 0,
        max_work: WorkUnits(limit.unwrap_or(bound.0)),
        max_scratch_bytes: layout.total_bytes(),
    };
    let decoder = Decoder::new(BackendRequest::Auto, 0xd6e8_feb8_6659_fd93).unwrap();
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
    )?;
    let mut stages = Vec::new();
    while job.next_stage().is_some() {
        match job.run_next() {
            StageProgress::Completed {
                stage,
                work,
                locator_degree,
                ..
            } => {
                if matches!(
                    format!("{stage:?}").as_str(),
                    "GuardThree" | "NewtonThree" | "GuardFour" | "NewtonFour"
                ) {
                    assert_eq!(locator_degree, 0, "a probe is not a BM observation");
                }
                stages.push((format!("{stage:?}"), work.0));
            }
            StageProgress::Failed(error) => {
                assert_eq!(job.run_next(), StageProgress::Failed(error));
                return job.finish().map(|_| unreachable!());
            }
        }
    }
    let report = job.finish()?;
    let Some(DecodeOutcome::Decoded { ids }) = report.outcome(0) else {
        panic!("expected decoded: {:?}", report.outcome(0));
    };
    Ok((ids.to_vec(), stages, report.work.0))
}

fn whole_row(which: usize) {
    for (c, beta, ids, expected) in [
        (
            6,
            3,
            vec![1, 2, 3],
            vec![
                ("GuardThree", 57),
                ("NewtonThree", 201),
                ("LeafThree", 841),
                ("FactorVerification", 872),
                ("Verification", 930),
                ("Canonicalization", 939),
            ],
        ),
        (
            7,
            4,
            vec![1, 2, 4, 7],
            vec![
                ("GuardThree", 58),
                ("GuardFour", 138),
                ("NewtonFour", 298),
                ("LeafFour", 2346),
                ("FactorVerification", 2395),
                ("Verification", 2477),
                ("Canonicalization", 2489),
            ],
        ),
    ] {
        if beta != which {
            continue;
        }
        let (actual, stages, used) = run(c, beta, &ids, DecodePlan::v3(), None).unwrap();
        assert_eq!(actual, ids);
        assert_eq!(
            stages,
            expected
                .iter()
                .map(|&(s, w)| (s.to_owned(), w))
                .collect::<Vec<_>>(),
            "explicit V3 whole-row d{beta} must skip BM and affine preparation"
        );
        assert_eq!(used, expected.last().unwrap().1);
        for &(_, threshold) in &expected {
            assert_eq!(
                run(c, beta, &ids, DecodePlan::v3(), Some(threshold - 1)),
                Err(DecodeError::WorkLimitExceeded)
            );
            let at = run(c, beta, &ids, DecodePlan::v3(), Some(threshold));
            if threshold < used {
                assert_eq!(at, Err(DecodeError::WorkLimitExceeded));
            } else {
                assert_eq!(at.unwrap().0, ids);
            }
        }
    }
}

#[test]
fn composed_bound_keeps_affine_and_adds_probes_and_leaves() {
    for (c, r, beta, want) in [
        (1, 1, 1, 472),
        (2, 2, 2, 1161),
        (3, 3, 3, 206478),
        (4, 4, 4, 505613),
        (18, 18, 18, 35497822),
        (72, 72, 72, 1679924956),
        (89, 89, 89, 3138619030),
        (18, 4, 4, 510933),
    ] {
        let (actual, v3_layout) = DecodePlan::v3()
            .complete_bound(&[c], &[Some(r)], beta, 0)
            .unwrap();
        let (_, v2_layout) = DecodePlan::v2()
            .complete_bound(&[c], &[Some(r)], beta, 0)
            .unwrap();
        assert_eq!(
            actual.0, want,
            "composed complete bound c={c} r={r} beta={beta}"
        );
        assert_eq!(
            v3_layout.total_bytes(),
            v2_layout.total_bytes(),
            "unchanged arena layout"
        );
    }
}

#[test]
fn public_whole_row_cubic() {
    whole_row(3);
}

#[test]
fn public_whole_row_quartic() {
    whole_row(4);
}
