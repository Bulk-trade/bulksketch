#![forbid(unsafe_code)]

use {
    crate::{
        BackendId, BackendRequest, DecodeError, DecodeFailure, DecodeLimits, DecodeOutcome,
        DecodePlan, DecodeRequest, DecodeScratch, Decoder, FrozenSketch, Gf64, MutableSketch,
        ParseLimits, ShapeLimits, SketchShape, SketchView, WorkUnits, decode_into,
    },
    std::{collections::BTreeSet, sync::Arc},
};

#[derive(Debug, PartialEq, Eq)]
pub enum Outcome {
    Equal,
    Decoded(Vec<u64>),
    Failed(DecodeFailure),
}

pub fn mix(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

pub fn rows(buckets: usize, count: usize, shift: u32) -> Vec<Vec<u64>> {
    let mut rows = vec![BTreeSet::new(); buckets];
    let mut index = 1;
    while rows.iter().any(|row| row.len() < count) {
        let id = mix(index) >> shift;
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

pub fn fixture(
    buckets: usize,
    capacity: usize,
    rows: &[Vec<u64>],
    backend: BackendId,
) -> (FrozenSketch<Gf64>, FrozenSketch<Gf64>) {
    let shape = Arc::new(
        SketchShape::new(
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
    let mut local = MutableSketch::new(shape, BackendRequest::Force(backend)).unwrap();
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

pub fn decode(
    local: &FrozenSketch<Gf64>,
    wire: &[u8],
    beta: usize,
    seed: u64,
    backend: BackendId,
    candidates: &[u64],
) -> Result<(Vec<Outcome>, WorkUnits), DecodeError> {
    decode_with_work(local, wire, beta, seed, backend, candidates, None)
}

pub fn decode_with_work(
    local: &FrozenSketch<Gf64>,
    wire: &[u8],
    beta: usize,
    seed: u64,
    backend: BackendId,
    candidates: &[u64],
    work: Option<WorkUnits>,
) -> Result<(Vec<Outcome>, WorkUnits), DecodeError> {
    let parse_limits = ParseLimits {
        max_wire_bytes: 100_000,
        max_buckets: 16,
        max_capacity_per_bucket: 89,
        max_total_syndrome_words: 1424,
    };
    let remote = SketchView::parse(wire, &parse_limits).unwrap();
    let local_zero = SketchView::<Gf64>::parse(local.encoded_v1().unwrap(), &parse_limits)
        .unwrap()
        .zero(0)
        .unwrap();
    let zero = local_zero != remote.zero(0).unwrap();
    let budgets: Vec<_> = (0..local.shape().bucket_count())
        .map(|row| beta.checked_sub(usize::from(row == 0 && zero)))
        .collect();
    let plan = DecodePlan::v1();
    let (max_work, layout) = plan
        .complete_bound(local.shape().capacities(), &budgets, beta, candidates.len())
        .unwrap();
    let limits = DecodeLimits {
        max_output_per_bucket: beta,
        max_candidate_inputs: candidates.len(),
        max_work: work.unwrap_or(max_work),
        max_scratch_bytes: layout.total_bytes(),
    };
    let mut scratch = DecodeScratch::new(&layout).unwrap();
    let decoder = Decoder::new(BackendRequest::Force(backend), seed).unwrap();
    let report = decode_into(
        DecodeRequest {
            local,
            remote,
            candidates,
            plan: &plan,
            limits: &limits,
        },
        &decoder,
        &mut scratch,
    )?;
    let outcomes = (0..report.bucket_count())
        .map(|bucket| match report.outcome(bucket).unwrap() {
            DecodeOutcome::Equal => Outcome::Equal,
            DecodeOutcome::Decoded { ids } => Outcome::Decoded(ids.to_vec()),
            DecodeOutcome::Failed { reason } => Outcome::Failed(reason),
        })
        .collect();
    Ok((outcomes, report.work))
}
