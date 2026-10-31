//! Shared helpers for comparing `bulksketch` with minisketch.
//!
//! A one-bucket `bulksketch` sketch stores the same odd syndromes as a 64-bit
//! minisketch of the same capacity, so a row's payload (the encoding without its
//! header) has exactly minisketch's serialized bytes. These helpers build both
//! sketches from the same IDs and decode them through each library's public API.
#![forbid(unsafe_code)]

use {
    bulksketch::{
        BackendRequest, DecodeLimits, DecodeOutcome, DecodePlan, DecodeRow, DecodeRowsRequest,
        DecodeScratch, Decoder, FrozenSketch, Gf64, MutableSketch, ShapeLimits, SketchShape,
        decode_rows_into,
    },
    minisketch_rs::Minisketch,
    std::sync::Arc,
};

/// Bytes before the syndrome payload in the encoding of a one-bucket sketch:
/// a 24-byte header, one 16-bit capacity and one zero-membership byte.
pub const ROW_PREFIX: usize = 24 + 2 + 1;

/// Fixed splitter seed, so test and benchmark runs are reproducible.
pub const SEED: u64 = 0xd6e8_feb8_6659_fd93;

/// SplitMix64 finalizer: a deterministic stream of well-mixed 64-bit IDs.
#[must_use]
pub fn mix(mut x: u64) -> u64 {
    x = x.wrapping_add(0x9e37_79b9_7f4a_7c15);
    x = (x ^ (x >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    x = (x ^ (x >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    x ^ (x >> 31)
}

/// `count` distinct nonzero IDs drawn from stream `stream`.
#[must_use]
pub fn ids(stream: u64, count: usize) -> Vec<u64> {
    let mut out = Vec::with_capacity(count);
    let mut i = 0;
    while out.len() < count {
        let id = mix(stream.wrapping_mul(0x1_0000_0001).wrapping_add(i));
        i += 1;
        if id != 0 && !out.contains(&id) {
            out.push(id);
        }
    }
    out
}

/// A one-bucket `bulksketch` sketch holding `ids`.
///
/// # Panics
/// If `capacity` is zero or above 65,535.
#[must_use]
pub fn bulk_row(capacity: usize, ids: &[u64]) -> FrozenSketch<Gf64> {
    let shape = SketchShape::new(
        &[capacity],
        &ShapeLimits {
            max_wire_bytes: ROW_PREFIX + capacity * 8,
            max_buckets: 1,
            max_capacity_per_bucket: capacity,
            max_total_syndrome_words: capacity,
        },
    )
    .unwrap();
    let mut sketch = MutableSketch::new(Arc::new(shape), BackendRequest::Auto).unwrap();
    for &id in ids {
        sketch.toggle(id);
    }
    sketch.freeze()
}

/// The syndrome payload of a one-bucket sketch, comparable with minisketch bytes.
///
/// # Panics
/// If the sketch has more than one bucket.
#[must_use]
pub fn payload(sketch: &FrozenSketch<Gf64>) -> &[u8] {
    assert_eq!(sketch.shape().bucket_count(), 1, "one-bucket sketch");
    &sketch.encoded_v1().unwrap()[ROW_PREFIX..]
}

/// A 64-bit minisketch of `capacity` holding `ids`, or `None` when the
/// implementation is not available on this CPU.
#[must_use]
pub fn minisketch(implementation: u32, capacity: usize, ids: &[u64]) -> Option<Minisketch> {
    let mut sketch = Minisketch::try_new(64, implementation, capacity).ok()?;
    for &id in ids {
        sketch.add(id);
    }
    Some(sketch)
}

/// Serialized bytes of a minisketch.
///
/// # Panics
/// If minisketch fails to serialize.
#[must_use]
pub fn minisketch_bytes(sketch: &Minisketch) -> Vec<u8> {
    let mut bytes = vec![0; sketch.serialized_size()];
    sketch.serialize(&mut bytes).unwrap();
    bytes
}

/// Decode a minisketch with an output buffer of its full capacity. The result is
/// sorted; `None` means minisketch reported a failure.
#[must_use]
pub fn minisketch_decode(sketch: &Minisketch) -> Option<Vec<u64>> {
    let mut out = vec![0; sketch.capacity()];
    let n = sketch.decode(&mut out).ok()?;
    out.truncate(n);
    out.sort_unstable();
    Some(out)
}

/// The result of decoding one row.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Row {
    /// Both sides are equal.
    Equal,
    /// The verified symmetric difference, ascending.
    Decoded(Vec<u64>),
    /// The row could not be decoded within its budget.
    Failed,
}

/// A reusable `bulksketch` decoder for requests of `rows` rows of one capacity,
/// with the output budget equal to the capacity and no candidate hints. It uses
/// decode plan V3 and keeps one scratch arena, like a long-running caller would.
pub struct BulkDecoder {
    rows: usize,
    limits: DecodeLimits,
    decoder: Decoder<Gf64>,
    scratch: DecodeScratch<Gf64>,
}

impl BulkDecoder {
    /// # Panics
    /// If the dimensions are not admissible.
    #[must_use]
    pub fn new(capacity: usize, rows: usize) -> Self {
        let capacities = vec![u16::try_from(capacity).unwrap(); rows];
        let budgets = vec![Some(capacity); rows];
        let (max_work, layout) = DecodePlan::v3()
            .complete_bound(&capacities, &budgets, capacity, 0)
            .unwrap();
        Self {
            rows,
            limits: DecodeLimits {
                max_output_per_bucket: capacity,
                max_candidate_inputs: 0,
                max_work,
                max_scratch_bytes: layout.total_bytes(),
            },
            decoder: Decoder::new(BackendRequest::Auto, SEED).unwrap(),
            scratch: DecodeScratch::new(&layout).unwrap(),
        }
    }

    /// Decode the rows in one request and return the number of decoded IDs, without
    /// copying results. Intended for timing.
    ///
    /// # Panics
    /// If the request is rejected (wrong row count or shape).
    pub fn decode_count(&mut self, rows: &[DecodeRow<'_, Gf64>]) -> usize {
        assert_eq!(rows.len(), self.rows, "row count");
        let report = decode_rows_into(
            DecodeRowsRequest {
                rows,
                plan: &DecodePlan::v3(),
                limits: &self.limits,
            },
            &self.decoder,
            &mut self.scratch,
        )
        .unwrap();
        (0..rows.len())
            .map(|i| match report.outcome(i) {
                Some(DecodeOutcome::Decoded { ids }) => ids.len(),
                _ => 0,
            })
            .sum()
    }

    /// Decode the rows in one request and return every row's outcome.
    ///
    /// # Panics
    /// If the request is rejected (wrong row count or shape).
    pub fn decode(&mut self, rows: &[DecodeRow<'_, Gf64>]) -> Vec<Row> {
        assert_eq!(rows.len(), self.rows, "row count");
        let report = decode_rows_into(
            DecodeRowsRequest {
                rows,
                plan: &DecodePlan::v3(),
                limits: &self.limits,
            },
            &self.decoder,
            &mut self.scratch,
        )
        .unwrap();
        (0..rows.len())
            .map(|i| match report.outcome(i).unwrap() {
                DecodeOutcome::Equal => Row::Equal,
                DecodeOutcome::Decoded { ids } => Row::Decoded(ids.to_vec()),
                DecodeOutcome::Failed { .. } => Row::Failed,
            })
            .collect()
    }
}

/// Decode one row: the local sketch against remote syndrome bytes.
#[must_use]
pub fn bulk_decode_row(local: &FrozenSketch<Gf64>, remote: &[u8]) -> Row {
    let capacity = usize::from(local.shape().capacities()[0]);
    BulkDecoder::new(capacity, 1).decode(&[DecodeRow {
        local,
        remote,
        candidates: &[],
    }])[0]
        .clone()
}

/// Sorted symmetric difference of two ID sets.
#[must_use]
pub fn symmetric_difference(a: &[u64], b: &[u64]) -> Vec<u64> {
    let mut out: Vec<u64> = a
        .iter()
        .filter(|x| !b.contains(x))
        .chain(b.iter().filter(|x| !a.contains(x)))
        .copied()
        .collect();
    out.sort_unstable();
    out
}
