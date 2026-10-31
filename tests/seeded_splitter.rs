#![forbid(unsafe_code)]

use {
    bulksketch::{
        BackendRequest, DecodeFailure, DecodeJob, DecodeLimits, DecodeOutcome, DecodePlan,
        DecodeRequest, DecodeScratch, Decoder, FrozenSketch, Gf64, MutableSketch, ParseLimits,
        ShapeLimits, SketchShape, SketchView, Stage, StageProgress, WorkUnits,
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
) -> (Vec<Outcome>, WorkUnits, usize) {
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
    let plan = DecodePlan::v2();
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
        max_work,
        max_scratch_bytes: layout.total_bytes(),
    };
    let decoder = Decoder::new(BackendRequest::Auto, seed).unwrap();
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
            StageProgress::Failed(error) => panic!("complete work bound: {error:?}"),
            StageProgress::Completed { .. } => {}
        }
    }
    let report = job.finish().unwrap();
    let outcomes = (0..report.bucket_count())
        .map(|bucket| match report.outcome(bucket).unwrap() {
            DecodeOutcome::Equal => Outcome::Equal,
            DecodeOutcome::Decoded { ids } => Outcome::Decoded(ids.to_vec()),
            DecodeOutcome::Failed { reason } => Outcome::Failed(reason),
        })
        .collect();
    (outcomes, report.work, traces)
}

#[test]
fn results_are_seed_invariant() {
    for (buckets, capacity) in [(16, 18), (16, 32), (4, 72), (1, 89)] {
        for kind in [0, 1, 24, 40] {
            for count in [0, capacity / 2, capacity, capacity + 1] {
                let mut rows = ids(buckets, count, kind);
                if kind == 1 && count == capacity / 2 {
                    rows[0].insert(0, 0);
                }
                let (local, remote) = fixture(capacity, &rows);
                let expected = decode(&local, &remote, capacity, 1, &[]).0;
                for (row, expected) in rows.iter().zip(&expected) {
                    if count == 0 {
                        assert_eq!(*expected, Outcome::Equal);
                    } else if count <= capacity {
                        assert_eq!(*expected, Outcome::Decoded(row.clone()), "exact set");
                    } else {
                        assert!(matches!(expected, Outcome::Failed(_)), "overflow fixture");
                    }
                }
                for seed in [0, u64::MAX, SEED, 1 << 63, 0x1234_5678_9abc_def0] {
                    let actual = decode(&local, &remote, capacity, seed, &[]).0;
                    assert_eq!(
                        actual, expected,
                        "seed={seed:#x} {buckets}x{capacity} d={count} kind={kind}"
                    );
                }
                // Hints include duplicates and a wrong ID; deflation still uses this seed.
                let candidates: Vec<_> = rows
                    .iter()
                    .flat_map(|row| row.iter().take(2))
                    .copied()
                    .chain([u64::MAX, u64::MAX])
                    .collect();
                assert_eq!(
                    decode(&local, &remote, capacity, SEED, &candidates).0,
                    expected
                );
            }
        }
    }
}

#[test]
fn seed_removes_structured_work_inflation() {
    let rows = ids(16, 32, 40);
    let (local, remote) = fixture(32, &rows);
    let fixed = decode(&local, &remote, 32, 1, &[]);
    let seeded = decode(&local, &remote, 32, SEED, &[]);
    assert_eq!(seeded.0, fixed.0);
    eprintln!(
        "fixed work={} traces={}; seeded work={} traces={}",
        fixed.1.0, fixed.2, seeded.1.0, seeded.2
    );
    // A fourfold bound leaves room for split-tree variation while excluding the
    // long prefix of unproductive traces on the 24-bit ID subspace.
    assert!(
        seeded.1.0 * 4 < fixed.1.0,
        "seed must cut structured decode work by more than 4x: fixed={} seeded={}",
        fixed.1.0,
        seeded.1.0
    );
}
