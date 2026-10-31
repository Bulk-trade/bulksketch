#![forbid(unsafe_code)]

use {
    crate::{
        BackendId, BackendRequest, DecodeError, DecodeFailure, DecodeJob, DecodeLimits,
        DecodeOutcome, DecodePlan, DecodeRequest, DecodeScratch, Decoder, FrozenSketch, Gf64,
        InsertScratch, MutableSketch, ParseLimits, ShapeLimits, SketchShape, SketchView, Stage,
        StageProgress, WorkUnits,
    },
    std::{collections::BTreeSet, sync::Arc},
};

const SEED: u64 = 0xd6e8_feb8_6659_fd93;

#[derive(Debug, PartialEq, Eq)]
enum Outcome {
    Equal,
    Decoded(Vec<u64>),
    Failed(DecodeFailure),
}

fn mix(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

fn ids(buckets: usize, count: usize, kind: u32) -> Vec<Vec<u64>> {
    let mut rows = vec![BTreeSet::new(); buckets];
    let mut index = 1;
    while rows.iter().any(|row| row.len() < count) {
        let id = match kind {
            0 => mix(index),
            1 => index,
            24 | 40 => mix(index) >> kind,
            _ => unreachable!(),
        };
        let bucket = usize::try_from(id % u64::try_from(buckets).unwrap()).unwrap();
        if id != 0 && rows[bucket].len() < count {
            rows[bucket].insert(id);
        }
        index += 1;
    }
    rows.into_iter()
        .map(|row| row.into_iter().collect())
        .collect()
}

fn fixture(capacity: usize, rows: &[Vec<u64>]) -> (FrozenSketch<Gf64>, FrozenSketch<Gf64>) {
    let shape = Arc::new(
        SketchShape::new(
            &vec![capacity; rows.len()],
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap(),
    );
    let mut local = MutableSketch::new(shape, BackendRequest::Auto).unwrap();
    for id in [0, u64::MAX, 0x8123_4567_89ab_cdef] {
        local.toggle(id);
    }
    let mut remote = local.clone();
    for (index, &id) in rows.iter().flatten().enumerate() {
        if index % 2 == 0 {
            local.toggle(id);
        } else {
            remote.toggle(id);
        }
    }
    (local.freeze(), remote.freeze())
}

fn decode(
    local: &FrozenSketch<Gf64>,
    remote: &FrozenSketch<Gf64>,
    capacity: usize,
    seed: u64,
    candidates: &[u64],
    backend: BackendRequest,
) -> (Vec<Outcome>, WorkUnits, usize) {
    decode_limited(local, remote, capacity, seed, candidates, backend, None).unwrap()
}

fn decode_limited(
    local: &FrozenSketch<Gf64>,
    remote: &FrozenSketch<Gf64>,
    capacity: usize,
    seed: u64,
    candidates: &[u64],
    backend: BackendRequest,
    work_limit: Option<WorkUnits>,
) -> Result<(Vec<Outcome>, WorkUnits, usize), DecodeError> {
    let parse_limits = ParseLimits {
        max_wire_bytes: 100_000,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 1424,
    };
    let remote = SketchView::parse(remote.encoded_v1().unwrap(), &parse_limits).unwrap();
    let zero = SketchView::<Gf64>::parse(local.encoded_v1().unwrap(), &parse_limits)
        .unwrap()
        .zero(0)
        .unwrap()
        != remote.zero(0).unwrap();
    let budgets: Vec<_> = (0..local.shape().bucket_count())
        .map(|bucket| capacity.checked_sub(usize::from(bucket == 0 && zero)))
        .collect();
    let plan = DecodePlan::v1();
    let (max_work, layout) = plan
        .complete_bound(
            local.shape().capacities(),
            &budgets,
            capacity,
            candidates.len(),
        )
        .unwrap();
    let limits = DecodeLimits {
        max_output_per_bucket: capacity,
        max_candidate_inputs: candidates.len(),
        max_work: work_limit.unwrap_or(max_work),
        max_scratch_bytes: layout.total_bytes(),
    };
    let decoder = Decoder::new(backend, seed).unwrap();
    let mut scratch = DecodeScratch::new(&layout).unwrap();
    let mut job = DecodeJob::new(
        DecodeRequest {
            local,
            remote,
            candidates,
            plan: &plan,
            limits: &limits,
        },
        &decoder,
        &mut scratch,
    )
    .unwrap();
    let mut traces = 0;
    while job.next_stage().is_some() {
        match job.run_next() {
            StageProgress::Completed {
                stage: Stage::Trace,
                ..
            } => traces += 1,
            StageProgress::Failed(error) => {
                if work_limit.is_some() {
                    break;
                }
                panic!("complete work bound: {error:?}");
            }
            StageProgress::Completed { .. } => {}
        }
    }
    let report = job.finish()?;
    let outcomes = (0..report.bucket_count())
        .map(|bucket| match report.outcome(bucket).unwrap() {
            DecodeOutcome::Equal => Outcome::Equal,
            DecodeOutcome::Decoded { ids } => Outcome::Decoded(ids.to_vec()),
            DecodeOutcome::Failed { reason } => Outcome::Failed(reason),
        })
        .collect();
    Ok((outcomes, report.work, traces))
}

fn available() -> bool {
    #[cfg(target_arch = "x86_64")]
    {
        std::is_x86_feature_detected!("avx512f") && std::is_x86_feature_detected!("vpclmulqdq")
    }
    #[cfg(not(target_arch = "x86_64"))]
    {
        false
    }
}
const PORTABLE: BackendRequest = BackendRequest::Force(BackendId::Portable);
const VECTOR: BackendRequest = BackendRequest::Force(BackendId::Vpclmul512);

#[test]
fn public_batch_order_parity_and_cow() {
    if !available() {
        return;
    }
    for (buckets, capacity) in [(16, 18), (16, 32), (4, 72), (1, 89)] {
        let shape = Arc::new(
            SketchShape::<Gf64>::new(
                &vec![capacity; buckets],
                &ShapeLimits {
                    max_wire_bytes: 100_000,
                    max_buckets: 16,
                    max_capacity_per_bucket: 89,
                    max_total_syndrome_words: 1424,
                },
            )
            .unwrap(),
        );
        let mut expected = MutableSketch::new(Arc::clone(&shape), PORTABLE).unwrap();
        let mut actual = MutableSketch::new(shape, VECTOR).unwrap();
        let mut scratch = InsertScratch::new(512, buckets).unwrap();
        let input: Vec<_> = (0..512)
            .map(|i| if i % 19 == 0 { 0 } else { mix(i % 83) })
            .collect();
        for width in [1, 8, 64, 512] {
            for reverse in [false, true] {
                let mut input = input.clone();
                if reverse {
                    input.reverse();
                }
                let old = actual.freeze();
                let old_bytes = old.encoded_v1().unwrap().to_vec();
                for chunk in input.chunks(width) {
                    actual.toggle_batch(chunk, &mut scratch).unwrap();
                    for &id in chunk {
                        expected.toggle(id);
                    }
                    assert_eq!(
                        actual.freeze().encoded_v1().unwrap(),
                        expected.freeze().encoded_v1().unwrap(),
                        "batch {buckets}x{capacity} width={width}"
                    );
                }
                assert_eq!(old.encoded_v1().unwrap(), old_bytes, "snapshot isolation");
                drop(old);
                // The last chunk populated a cache; this mutation uses unique state.
                actual.toggle(0);
                expected.toggle(0);
                assert_eq!(
                    actual.freeze().encoded_v1().unwrap(),
                    expected.freeze().encoded_v1().unwrap(),
                    "unique cache invalidation"
                );
            }
        }
        let mut sibling = actual.clone();
        let frozen = actual.freeze();
        let bytes = frozen.encoded_v1().unwrap().to_vec();
        sibling.toggle_batch(&input, &mut scratch).unwrap();
        assert_eq!(
            frozen.encoded_v1().unwrap(),
            bytes,
            "mutable clone isolation"
        );
    }
}

#[test]
fn forced_decode_outcomes_work_and_bytes() {
    if !available() {
        return;
    }
    for (buckets, capacity) in [(16, 18), (16, 32), (4, 72), (1, 89)] {
        for kind in [0, 24, 40] {
            for count in [0, 1, 5, capacity, capacity + 1] {
                let mut rows = ids(buckets, count, kind);
                if kind == 40 && count == 0 {
                    rows[0].push(0);
                }
                if kind == 24 && count == 1 {
                    rows[0].insert(0, 0);
                }
                let (local, remote) = fixture(capacity, &rows);
                for seed in [1, SEED, u64::MAX] {
                    for hints in [false, true] {
                        let candidates: Vec<_> = if hints {
                            rows.iter()
                                .flat_map(|r| r.iter().take(2))
                                .copied()
                                .chain([0, u64::MAX, u64::MAX])
                                .collect()
                        } else {
                            vec![]
                        };
                        let expected =
                            decode(&local, &remote, capacity, seed, &candidates, PORTABLE);
                        let actual = decode(&local, &remote, capacity, seed, &candidates, VECTOR);
                        assert_eq!(
                            actual, expected,
                            "decode {buckets}x{capacity} d={count} kind={kind} seed={seed:#x} \
                             hints={hints}"
                        );
                        if count == 5 && kind == 0 && seed == SEED && !hints {
                            let tight = WorkUnits(expected.1.0.checked_sub(1).unwrap());
                            for backend in [PORTABLE, VECTOR] {
                                assert_eq!(
                                    decode_limited(
                                        &local,
                                        &remote,
                                        capacity,
                                        seed,
                                        &candidates,
                                        backend,
                                        Some(tight)
                                    )
                                    .unwrap_err(),
                                    DecodeError::WorkLimitExceeded,
                                    "late request failure {backend:?}"
                                );
                            }
                        }
                        if count <= capacity {
                            for (row, outcome) in rows.iter().zip(&actual.0) {
                                assert_eq!(
                                    *outcome,
                                    if row.is_empty() {
                                        Outcome::Equal
                                    } else {
                                        Outcome::Decoded(row.clone())
                                    },
                                    "exact retained inputs"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}
