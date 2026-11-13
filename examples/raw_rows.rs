//! Decoding many one-bucket rows at once from raw syndrome bytes.
//!
//! Some applications carry sketch data inside their own message format and do
//! not want the full encoding with its header. `decode_rows_into` takes each
//! row as bare syndrome bytes: 8 bytes per unit of capacity, little-endian, in
//! the order the sketch stores them. All rows in the batch are decoded in one
//! call with one scratch arena, and each row succeeds or fails on its own.
//!
//! Raw rows have no place for ID 0 (the full encoding stores it as a separate
//! flag), so an ID 0 held only by the remote side cannot be recovered this way.
//!
//! Run it with:
//!
//! ```sh
//! cargo run --release --example raw_rows
//! ```

use {
    bulksketch::{
        BackendRequest, DecodeLimits, DecodePlan, DecodeRow, DecodeRowsRequest, DecodeScratch,
        Decoder, FrozenSketch, Gf64, MutableSketch, ParseLimits, ShapeLimits, SketchShape,
        SketchView, decode_rows_into,
    },
    std::{error::Error, sync::Arc},
};

const CAPACITY: usize = 18;
const ROWS: usize = 3;

fn one_row_sketch(ids: &[u64]) -> Result<FrozenSketch<Gf64>, Box<dyn Error>> {
    let shape = Arc::new(SketchShape::new(
        &[CAPACITY],
        &ShapeLimits {
            max_wire_bytes: 4096,
            max_buckets: 1,
            max_capacity_per_bucket: CAPACITY,
            max_total_syndrome_words: CAPACITY,
        },
    )?);
    let mut sketch = MutableSketch::new(shape, BackendRequest::Auto)?;
    for &id in ids {
        sketch.toggle(id);
    }
    Ok(sketch.freeze())
}

/// `count` IDs spread over the whole `u64` range, like hashes.
fn many_ids(count: u64) -> Vec<u64> {
    (1..=count)
        .map(|n| n.wrapping_mul(0x9e37_79b9_7f4a_7c15))
        .collect()
}

/// The raw syndrome bytes of a one-bucket sketch, as an application would put
/// them in its own message.
fn raw_row(sketch: &FrozenSketch<Gf64>) -> Result<Vec<u8>, Box<dyn Error>> {
    let view = SketchView::<Gf64>::parse(
        sketch.encoded_v1()?,
        &ParseLimits {
            max_wire_bytes: 4096,
            max_buckets: 1,
            max_capacity_per_bucket: CAPACITY,
            max_total_syndrome_words: CAPACITY,
        },
    )?;
    let mut bytes = Vec::with_capacity(8 * CAPACITY);
    for index in 0..CAPACITY {
        let word = view
            .odd_syndrome(0, index)
            .expect("index is below the capacity");
        bytes.extend_from_slice(&word.to_le_bytes());
    }
    Ok(bytes)
}

fn main() -> Result<(), Box<dyn Error>> {
    // Three independent rows, for example three topics that two peers each
    // track. Each pair of sets differs in a different way.
    let local = [
        one_row_sketch(&[1, 2, 3])?,
        one_row_sketch(&[7, 8])?,
        one_row_sketch(&[100])?,
    ];
    let remote = [
        // Equal to the local row.
        raw_row(&one_row_sketch(&[1, 2, 3])?)?,
        // Differs from the local row by 8, 9 and 10.
        raw_row(&one_row_sketch(&[7, 9, 10])?)?,
        // Far too many differences for capacity 18.
        raw_row(&one_row_sketch(&many_ids(40))?)?,
    ];

    let rows: Vec<DecodeRow<'_, Gf64>> = local
        .iter()
        .zip(&remote)
        .map(|(local, remote)| DecodeRow {
            local,
            remote,
            candidates: &[],
        })
        .collect();

    let plan = DecodePlan::v3();
    let (max_work, layout) = plan.complete_bound(
        &[CAPACITY as u16; ROWS],
        &[Some(CAPACITY); ROWS],
        CAPACITY,
        0,
    )?;
    let limits = DecodeLimits {
        max_output_per_bucket: CAPACITY,
        max_candidate_inputs: 0,
        max_work,
        max_scratch_bytes: layout.total_bytes(),
    };
    let decoder = Decoder::new(BackendRequest::Auto, 0x5eed)?;
    let mut scratch = DecodeScratch::new(&layout)?;

    let report = decode_rows_into(
        DecodeRowsRequest {
            rows: &rows,
            plan: &plan,
            limits: &limits,
        },
        &decoder,
        &mut scratch,
    )?;
    for row in 0..report.bucket_count() {
        let outcome = report.outcome(row).expect("row index is in range");
        println!("row {row}: {outcome:?}");
    }
    Ok(())
}
