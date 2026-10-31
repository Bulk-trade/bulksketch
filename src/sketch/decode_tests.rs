#![forbid(unsafe_code)]

use {
    super::*,
    crate::{
        BackendRequest, DecodeError, DecodeFailure, Gf64, Stage, StageProgress, WorkUnits,
        field::reference,
    },
    std::sync::Arc,
};

fn make_shape(capacities: &[usize]) -> Arc<SketchShape<Gf64>> {
    Arc::new(
        SketchShape::new(
            capacities,
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap(),
    )
}

fn sketch(shape: &Arc<SketchShape<Gf64>>, ids: &[u64]) -> FrozenSketch<Gf64> {
    let mut sketch = MutableSketch::new(Arc::clone(shape), BackendRequest::Auto).unwrap();
    for &id in ids {
        sketch.toggle(id);
    }
    sketch.freeze()
}

fn view(bytes: &[u8]) -> SketchView<'_, Gf64> {
    SketchView::parse(
        bytes,
        &ParseLimits {
            max_wire_bytes: 100_000,
            max_buckets: 16,
            max_capacity_per_bucket: 89,
            max_total_syndrome_words: 1424,
        },
    )
    .unwrap()
}

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Equal,
    Decoded(Vec<u64>),
    Failed(DecodeFailure),
}

#[derive(Debug, PartialEq, Eq)]
struct Observed {
    rows: Vec<Outcome>,
    work: WorkUnits,
    peak: usize,
}

fn observe(report: &DecodeReport<'_>) -> Observed {
    Observed {
        rows: (0..report.bucket_count())
            .map(|b| match report.outcome(b).unwrap() {
                DecodeOutcome::Equal => Outcome::Equal,
                DecodeOutcome::Decoded { ids } => Outcome::Decoded(ids.to_vec()),
                DecodeOutcome::Failed { reason } => Outcome::Failed(reason),
            })
            .collect(),
        work: report.work,
        peak: report.peak_scratch_bytes,
    }
}

fn layout(request: &DecodeRequest<'_, Gf64>) -> (WorkUnits, ScratchLayout) {
    let beta = request.limits.max_output_per_bucket;
    let zero = (request.local.state.zero_words[0] & 1 != 0) != request.remote.zero(0).unwrap();
    let budgets: Vec<_> = (0..request.local.shape().bucket_count())
        .map(|b| beta.checked_sub(usize::from(b == 0 && zero)))
        .collect();
    request
        .plan
        .complete_bound(
            request.local.shape().capacities(),
            &budgets,
            beta,
            request.candidates.len(),
        )
        .unwrap()
}

fn limits(beta: usize, candidates: usize) -> DecodeLimits {
    DecodeLimits {
        max_output_per_bucket: beta,
        max_candidate_inputs: candidates,
        max_work: WorkUnits(u64::MAX),
        max_scratch_bytes: usize::MAX,
    }
}

fn run(
    request: DecodeRequest<'_, Gf64>,
    staged: bool,
    scratch: &mut DecodeScratch<Gf64>,
) -> Result<(Observed, Vec<StageProgress>), DecodeError> {
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let mut progress = Vec::new();
    let report = if staged {
        let mut job = DecodeJob::new(request, &decoder, scratch)?;
        while job.next_stage().is_some() {
            progress.push(job.run_next());
        }
        job.finish()?
    } else {
        decode_into(request, &decoder, scratch)?
    };
    Ok((observe(&report), progress))
}

fn verify(request: &DecodeRequest<'_, Gf64>, result: &Observed) {
    for (bucket, outcome) in result.rows.iter().enumerate() {
        let ids = match outcome {
            Outcome::Equal => &[][..],
            Outcome::Decoded(ids) => ids,
            Outcome::Failed(_) => continue,
        };
        assert!(
            ids.len() <= request.limits.max_output_per_bucket,
            "total beta includes zero"
        );
        assert!(
            ids.windows(2).all(|p| p[0] < p[1]),
            "canonical original IDs"
        );
        assert!(
            ids.iter()
                .all(|&id| request.local.shape().permits_id(bucket, id)),
            "decoded root must route back to its row"
        );
        let zero = bucket == 0
            && (request.local.state.zero_words[0] & 1 != 0) != request.remote.zero(0).unwrap();
        assert_eq!(ids.contains(&0), zero, "verified zero channel");
        let capacity = usize::from(request.local.shape().capacities()[bucket]);
        let offset: usize = request.local.shape().capacities()[..bucket]
            .iter()
            .map(|&c| usize::from(c))
            .sum();
        for index in 0..capacity {
            let mut syndrome = 0;
            for &id in ids.iter().filter(|&&id| id != 0) {
                let mut power = 1;
                for _ in 0..=2 * index {
                    power = reference::mul::<Gf64>(power, id);
                }
                syndrome ^= power;
            }
            assert_eq!(
                syndrome,
                request.local.state.words[offset + index]
                    ^ request.remote.odd_syndrome(bucket, index).unwrap(),
                "every success re-encodes every syndrome: bucket={bucket} index={index}"
            );
        }
    }
}

fn check_exact(capacity: usize, buckets: usize, beta: usize, count: usize, hints: usize) {
    let shape = make_shape(&vec![capacity; buckets]);
    let bucket = buckets - 1;
    let mut ids: Vec<_> = (1..=count)
        .map(|i| ((i as u64) * buckets as u64 + bucket as u64) | (1 << 63))
        .collect();
    if count != 0 && bucket == 0 {
        ids[0] = 0;
    }
    let common: Vec<_> = (0..buckets)
        .map(|b| 0x4000_0000_0000_0000 | b as u64)
        .collect();
    let local = sketch(&shape, &common);
    let remote = sketch(&shape, &[common.as_slice(), &ids].concat());
    let bytes = remote.encoded_v1().unwrap();
    let mut candidates = match hints {
        0 => vec![],
        1 => ids.iter().step_by(2).copied().collect(),
        2 => ids.clone(),
        _ => vec![0x1234, 0x5678, u64::MAX],
    };
    if hints != 0 {
        candidates.extend_from_within(..);
        candidates.extend([0, 0]);
        candidates.reverse();
    }
    let plan = DecodePlan::v1();
    let caps = limits(beta, candidates.len());
    let request = DecodeRequest {
        local: &local,
        remote: view(bytes),
        candidates: &candidates,
        plan: &plan,
        limits: &caps,
    };
    let (work, required) = layout(&request);
    let caps = DecodeLimits {
        max_work: work,
        max_scratch_bytes: required.total_bytes(),
        ..caps
    };
    let request = DecodeRequest {
        limits: &caps,
        ..request
    };
    let mut scratch = DecodeScratch::new(&required).unwrap();
    let direct = run(request, false, &mut scratch).unwrap().0;
    let (staged, progress) = run(request, true, &mut scratch).unwrap();
    assert_eq!(
        direct, staged,
        "same publication/work: B={buckets} c={capacity} beta={beta} d={count} hints={hints}"
    );
    if count > 0 && count <= beta {
        let expected_hits = ids
            .iter()
            .filter(|&&id| id != 0 && candidates.contains(&id))
            .count();
        let expected_degree = ids.iter().filter(|&&id| id != 0).count();
        assert!(progress.iter().any(|p| matches!(p, StageProgress::Completed { stage: Stage::CandidateEvaluation, locator_degree, candidate_hits, .. } if *locator_degree == expected_degree && *candidate_hits == expected_hits)), "normalized candidate hits and original locator degree");
    }
    if let Some(StageProgress::Completed { work, .. }) = progress.last() {
        assert_eq!(
            *work, direct.work,
            "completed progress includes all charged request work"
        );
    }
    verify(&request, &direct);
    ids.sort_unstable();
    if count <= beta {
        let expected = if ids.is_empty() {
            Outcome::Equal
        } else {
            Outcome::Decoded(ids)
        };
        assert_eq!(
            direct.rows[bucket], expected,
            "exact recovery through beta: B={buckets} c={capacity} beta={beta} d={count} \
             hints={hints}"
        );
    } else {
        assert!(
            matches!(direct.rows[bucket], Outcome::Failed(_)),
            "protected interval rejects overflow: B={buckets} c={capacity} beta={beta} d={count} \
             hints={hints}"
        );
    }
    assert!(direct.work <= work);
}

#[test]
fn decode_exact_and_protected_interval() {
    for capacity in [18, 72, 89] {
        for buckets in [1, 4, 16] {
            let beta = capacity.min(64);
            let counts: Vec<_> = if buckets == 1 {
                (0..=beta).collect()
            } else {
                [0, 1, 2, 3, 4, 8, 16, 32, 48, 64, beta]
                    .into_iter()
                    .filter(|&d| d <= beta)
                    .collect()
            };
            for count in counts {
                for hints in 0..4 {
                    check_exact(capacity, buckets, beta, count, hints);
                }
            }
            if beta < capacity {
                for count in [beta + 1, 2 * capacity - beta] {
                    for hints in 0..4 {
                        check_exact(capacity, buckets, beta, count, hints);
                    }
                }
            }
        }
    }
    for count in 17..=20 {
        for hints in 0..4 {
            check_exact(18, 4, 16, count, hints);
        }
    }
}

#[test]
fn decode_zero_and_mixed_vectors() {
    let shape = make_shape(&[1, 1]);
    let local = sketch(&shape, &[]);
    let remote = sketch(&shape, &[0]);
    let plan = DecodePlan::v1();
    for line in include_str!("../../tests/vectors/failure-v1.tsv")
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
    {
        let fields: Vec<_> = line.split_whitespace().collect();
        let mut caps = limits(0, fields[1].parse().unwrap());
        caps.max_scratch_bytes = usize::MAX;
        let request = DecodeRequest {
            local: &local,
            remote: view(remote.encoded_v1().unwrap()),
            candidates: &[1],
            plan: &plan,
            limits: &caps,
        };
        let (_, required) = layout(&request);
        for staged in [false, true] {
            let mut scratch = DecodeScratch::new(&required).unwrap();
            scratch.outcomes.truncate(fields[2].parse().unwrap());
            let actual = run(request, staged, &mut scratch);
            let observed = match actual {
                Err(error) => format!("{error:?}"),
                Ok((result, _)) => {
                    assert_eq!(
                        result.rows,
                        [
                            Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
                            Outcome::Equal
                        ]
                    );
                    assert_eq!(result.work, WorkUnits(8), "admission golden work");
                    "DegreeExceedsBudget,Equal".to_owned()
                }
            };
            assert_eq!(
                observed, fields[3],
                "admission endpoints agree: {} staged={staged}",
                fields[0]
            );
        }
    }
    for beta in [0, 1] {
        for zero in [false, true] {
            let remote = sketch(&shape, if zero { &[0] } else { &[] });
            let caps = limits(beta, 2);
            let request = DecodeRequest {
                local: &local,
                remote: view(remote.encoded_v1().unwrap()),
                candidates: &[0, 0],
                plan: &plan,
                limits: &caps,
            };
            let (_, required) = layout(&request);
            for staged in [false, true] {
                let result = run(request, staged, &mut DecodeScratch::new(&required).unwrap())
                    .unwrap()
                    .0;
                let expected = match (zero, beta) {
                    (false, _) => Outcome::Equal,
                    (true, 0) => Outcome::Failed(DecodeFailure::DegreeExceedsBudget),
                    _ => Outcome::Decoded(vec![0]),
                };
                assert_eq!(
                    result.rows[0], expected,
                    "zero is never Equal and consumes a slot"
                );
                verify(&request, &result);
            }
        }
    }
    check_zero_work_vectors(plan);
}

fn check_zero_work_vectors(plan: DecodePlan) {
    let shape = make_shape(&[2]);
    let local = sketch(&shape, &[]);
    for line in include_str!("../../tests/vectors/work-zero-v1.tsv")
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        let values: Vec<u64> = line
            .split_whitespace()
            .map(|s| s.parse().unwrap())
            .collect();
        let [zero, beta, _, prefix, verify_charge, canonicalize] = values[..] else {
            panic!("work vector")
        };
        let remote = sketch(&shape, if zero == 0 { &[1] } else { &[0, 1] });
        for work in [
            prefix + verify_charge - 1,
            prefix + verify_charge,
            prefix + verify_charge + canonicalize,
        ] {
            let mut caps = limits(usize::try_from(beta).unwrap(), 0);
            caps.max_work = WorkUnits(work);
            let request = DecodeRequest {
                local: &local,
                remote: view(remote.encoded_v1().unwrap()),
                candidates: &[],
                plan: &plan,
                limits: &caps,
            };
            let (_, required) = layout(&request);
            for staged in [false, true] {
                let result = run(request, staged, &mut DecodeScratch::new(&required).unwrap());
                if work < prefix + verify_charge + canonicalize {
                    assert_eq!(
                        result.map(|_| ()),
                        Err(DecodeError::WorkLimitExceeded),
                        "total-beta verification/canonicalization limits"
                    );
                } else {
                    let result = result.unwrap().0;
                    assert_eq!(result.work, WorkUnits(work), "exact zero-slot work vector");
                    assert_eq!(
                        result.rows[0],
                        Outcome::Decoded(if zero == 0 { vec![1] } else { vec![0, 1] }),
                        "original zero is prepended to verified roots"
                    );
                    verify(&request, &result);
                }
            }
        }
    }
}

#[test]
fn decode_request_failure_is_terminal() {
    let shape = make_shape(&[1, 1]);
    let local = sketch(&shape, &[]);
    let remote = sketch(&shape, &[2, 1]);
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let plan = DecodePlan::v1();
    let mut caps = limits(1, 0);
    caps.max_work = WorkUnits(301);
    let request = DecodeRequest {
        local: &local,
        remote: view(remote.encoded_v1().unwrap()),
        candidates: &[],
        plan: &plan,
        limits: &caps,
    };
    let (_, required) = layout(&request);
    let mut scratch = DecodeScratch::new(&required).unwrap();
    assert_eq!(
        decode_into(request, &decoder, &mut scratch).map(|_| ()),
        Err(DecodeError::WorkLimitExceeded),
        "later work error suppresses the earlier successful row"
    );
    let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
    let mut failed_at = None;
    while let Some(stage) = job.next_stage() {
        if job.run_next() == StageProgress::Failed(DecodeError::WorkLimitExceeded) {
            failed_at = Some(stage);
        }
    }
    assert_eq!(
        failed_at,
        Some(Stage::Canonicalization),
        "row zero completes before row one's Compare exhausts"
    );
    assert_eq!(
        job.run_next(),
        StageProgress::Failed(DecodeError::WorkLimitExceeded),
        "request failure is sticky"
    );
    assert_eq!(
        job.finish().map(|_| ()),
        Err(DecodeError::WorkLimitExceeded),
        "no report after request failure"
    );
}

#[test]
fn decode_admission_order_and_storage() {
    let shape = make_shape(&[1, 1]);
    let local = sketch(&shape, &[]);
    let remote = sketch(&shape, &[0]);
    let other_shape = make_shape(&[2, 2]);
    let mismatch = sketch(&other_shape, &[]);
    let plan = DecodePlan::v1();
    let mut caps = limits(2, 0);
    caps.max_work = WorkUnits(0);
    caps.max_scratch_bytes = 0;
    let required = ScratchLayout::for_plan(&plan, &[1, 1], &[Some(0), Some(0)], 0, 0).unwrap();
    let mut scratch = DecodeScratch::new(&required).unwrap();
    scratch.outcomes.clear();
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    for staged in [false, true] {
        let check = |caps: &DecodeLimits,
                     remote,
                     plan: &DecodePlan,
                     scratch: &mut DecodeScratch<Gf64>,
                     expected| {
            let request = DecodeRequest {
                local: &local,
                remote,
                candidates: &[1],
                plan,
                limits: caps,
            };
            assert_eq!(
                run(request, staged, scratch).map(|_| ()),
                Err(expected),
                "constructor precedence staged={staged}"
            );
        };
        check(
            &caps,
            view(mismatch.encoded_v1().unwrap()),
            &plan,
            &mut scratch,
            DecodeError::ShapeMismatch,
        );
        check(
            &caps,
            view(remote.encoded_v1().unwrap()),
            &plan,
            &mut scratch,
            DecodeError::InvalidPlan,
        );
        caps.max_output_per_bucket = 0;
        check(
            &caps,
            view(remote.encoded_v1().unwrap()),
            &plan,
            &mut scratch,
            DecodeError::CandidateLimitExceeded,
        );
        caps.max_candidate_inputs = 1;
        check(
            &caps,
            view(remote.encoded_v1().unwrap()),
            &plan,
            &mut scratch,
            DecodeError::WorkLimitExceeded,
        );
        caps.max_work = WorkUnits(3);
        check(
            &caps,
            view(remote.encoded_v1().unwrap()),
            &plan,
            &mut scratch,
            DecodeError::ScratchTooSmall,
        );
        caps = limits(2, 0);
        caps.max_work = WorkUnits(0);
        caps.max_scratch_bytes = 0;
    }
    let caps = limits(1, 1);
    let request = DecodeRequest {
        local: &local,
        remote: view(remote.encoded_v1().unwrap()),
        candidates: &[1],
        plan: &plan,
        limits: &caps,
    };
    check_storage_admission(request, decoder);
}

fn check_storage_admission(request: DecodeRequest<'_, Gf64>, decoder: Decoder<Gf64>) {
    let (_, required) = layout(&request);
    for segment in 0..5 {
        let mut arena = DecodeScratch::new(&required).unwrap();
        match segment {
            0 => arena.words.clear(),
            1 => arena.raw.clear(),
            2 => arena.factors.clear(),
            3 => arena.ids.clear(),
            _ => arena.outcomes.clear(),
        }
        assert_eq!(
            DecodeJob::new(request, &decoder, &mut arena).map(|_| ()),
            Err(DecodeError::ScratchTooSmall),
            "every nonempty segment is admitted"
        );
    }
    let (_, required) = layout(&request);
    let mut exact_caps = *request.limits;
    exact_caps.max_scratch_bytes = required.total_bytes() - 1;
    let request = DecodeRequest {
        limits: &exact_caps,
        ..request
    };
    assert_eq!(
        run(request, true, &mut DecodeScratch::new(&required).unwrap()).map(|_| ()),
        Err(DecodeError::ScratchTooSmall),
        "required byte cap includes outcomes and results"
    );
}

#[test]
fn decode_rejects_wrong_row_roots() {
    let shape = make_shape(&[2, 2]);
    let local = sketch(&shape, &[]);
    let remote = sketch(&shape, &[1]);
    let mut bytes = remote.encoded_v1().unwrap().to_vec();
    let first = 29;
    let wrong_row = bytes[first + 16..first + 32].to_vec();
    bytes[first..first + 16].copy_from_slice(&wrong_row);
    bytes[first + 16..].fill(0);
    let caps = limits(1, 1);
    let plan = DecodePlan::v1();
    let request = DecodeRequest {
        local: &local,
        remote: view(&bytes),
        candidates: &[1],
        plan: &plan,
        limits: &caps,
    };
    let (_, required) = layout(&request);
    for staged in [false, true] {
        let result = run(request, staged, &mut DecodeScratch::new(&required).unwrap())
            .unwrap()
            .0;
        assert_eq!(
            result.rows,
            [
                Outcome::Failed(DecodeFailure::InvalidLocator),
                Outcome::Equal
            ],
            "algebraic roots must obey original-ID routing"
        );
    }
}

#[test]
fn decode_dirty_scratch_and_drop() {
    let shape = make_shape(&[18; 4]);
    let local = sketch(&shape, &[0, 1, 7]);
    let remote = sketch(&shape, &[1, 2, 3, 4, 8, 12, 16]);
    let hints = [16, 0, 2, 2, 8, 0, 999, 12];
    let caps = limits(8, hints.len());
    let plan = DecodePlan::v1();
    let request = DecodeRequest {
        local: &local,
        remote: view(remote.encoded_v1().unwrap()),
        candidates: &hints,
        plan: &plan,
        limits: &caps,
    };
    let (_, required) = layout(&request);
    let mut scratch = DecodeScratch::new(&required).unwrap();
    let address = (
        scratch.words.as_ptr(),
        scratch.raw.as_ptr(),
        scratch.factors.as_ptr(),
        scratch.ids.as_ptr(),
        scratch.outcomes.as_ptr(),
    );
    let decoder = Decoder::new(BackendRequest::Auto, 1).unwrap();
    let expected = run(request, true, &mut scratch).unwrap();
    for garbage in [0, 1, u64::MAX, 0xdead_beef_1234_5678] {
        scratch.words.fill(garbage);
        scratch.ids.fill(garbage);
        for raw in &mut scratch.raw {
            raw.lo = garbage;
            raw.hi = !garbage;
        }
        for frame in &mut scratch.factors {
            frame.coefficient_start = garbage;
            frame.coefficient_len = garbage;
            frame.next_direction = u32::MAX;
            frame.split_checked = u32::MAX;
        }
        {
            let mut job = DecodeJob::new(request, &decoder, &mut scratch).unwrap();
            job.run_next();
            job.run_next();
        }
        let observed = run(request, true, &mut scratch).unwrap();
        assert_eq!(
            observed, expected,
            "dirty scratch/drop cannot change IDs, counters, stages or work"
        );
        verify(&request, &observed.0);
        assert_eq!(run(request, false, &mut scratch).unwrap().0, observed.0);
    }
    assert_eq!(
        (
            scratch.words.as_ptr(),
            scratch.raw.as_ptr(),
            scratch.factors.as_ptr(),
            scratch.ids.as_ptr(),
            scratch.outcomes.as_ptr()
        ),
        address,
        "decode never grows a supplied arena"
    );
}
