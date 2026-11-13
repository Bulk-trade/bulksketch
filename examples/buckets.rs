//! A sketch with 16 buckets. Each bucket decodes on its own, so a bucket that
//! holds too many differences fails without spoiling the others, and the peers
//! only need a fallback for that one bucket.
//!
//! Run it with:
//!
//! ```sh
//! cargo run --release --example buckets
//! ```

use {
    bulksketch::{
        BackendRequest, DecodeLimits, DecodeOutcome, DecodePlan, DecodeRequest, DecodeScratch,
        Decoder, FrozenSketch, Gf64, InsertScratch, MutableSketch, ParseLimits, ShapeLimits,
        SketchShape, SketchView, decode_into,
    },
    std::{collections::BTreeSet, error::Error, sync::Arc},
};

const BUCKETS: usize = 16;
const CAPACITY: usize = 8;

/// Stand-in for real 64-bit IDs such as hashes.
fn id(n: u64) -> u64 {
    n.wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

/// Build a frozen sketch from many IDs at once. `toggle_batch` sorts the IDs
/// into their buckets in one pass, which is faster than one `toggle` per ID.
fn sketch_of(
    shape: &Arc<SketchShape<Gf64>>,
    ids: &[u64],
) -> Result<FrozenSketch<Gf64>, Box<dyn Error>> {
    let mut sketch = MutableSketch::new(Arc::clone(shape), BackendRequest::Auto)?;
    let mut insert_scratch = InsertScratch::new(ids.len(), BUCKETS)?;
    sketch.toggle_batch(ids, &mut insert_scratch)?;
    Ok(sketch.freeze())
}

fn main() -> Result<(), Box<dyn Error>> {
    let shape_limits = ShapeLimits {
        max_wire_bytes: 8192,
        max_buckets: BUCKETS,
        max_capacity_per_bucket: CAPACITY,
        max_total_syndrome_words: BUCKETS * CAPACITY,
    };
    // 16 buckets of capacity 8: up to 8 differences per bucket, 128 in total.
    let shape = Arc::new(SketchShape::<Gf64>::new(
        &[CAPACITY; BUCKETS],
        &shape_limits,
    )?);

    // 100,000 IDs in common, plus 30 IDs that only Bob has. An ID goes to
    // bucket `id % 16`, so the 30 differences spread over the buckets unevenly.
    let common: Vec<u64> = (1..=100_000).map(id).collect();
    let mut bob_only: Vec<u64> = (200_001..=200_030).map(id).collect();
    // Add 10 more differences that all land in bucket 3, so that bucket holds
    // more than its capacity of 8.
    bob_only.extend(
        (300_000..)
            .map(id)
            .filter(|&id| shape.bucket_for(id) == 3)
            .take(10),
    );

    let alice_ids = common.clone();
    let bob_ids: Vec<u64> = common.iter().chain(&bob_only).copied().collect();
    let alice = sketch_of(&shape, &alice_ids)?;
    let bob = sketch_of(&shape, &bob_ids)?;

    let message = bob.encoded_v1()?.to_vec();
    println!(
        "Bob sends {} bytes; {} differences in total",
        message.len(),
        bob_only.len()
    );

    let remote = SketchView::parse(
        &message,
        &ParseLimits {
            max_wire_bytes: 8192,
            max_buckets: BUCKETS,
            max_capacity_per_bucket: CAPACITY,
            max_total_syndrome_words: BUCKETS * CAPACITY,
        },
    )?;

    let plan = DecodePlan::v3();
    let (max_work, layout) = plan.complete_bound(
        &[CAPACITY as u16; BUCKETS],
        &[Some(CAPACITY); BUCKETS],
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
    let report = decode_into(
        DecodeRequest {
            local: &alice,
            remote,
            candidates: &[],
            plan: &plan,
            limits: &limits,
        },
        &decoder,
        &mut scratch,
    )?;

    let mut recovered = BTreeSet::new();
    let mut failed_buckets = Vec::new();
    for bucket in 0..report.bucket_count() {
        match report.outcome(bucket) {
            Some(DecodeOutcome::Equal) => println!("bucket {bucket:2}: equal"),
            Some(DecodeOutcome::Decoded { ids }) => {
                println!("bucket {bucket:2}: decoded, differences: {}", ids.len());
                recovered.extend(ids.iter().copied());
            }
            Some(DecodeOutcome::Failed { reason }) => {
                println!("bucket {bucket:2}: failed ({reason:?})");
                failed_buckets.push(bucket);
            }
            None => unreachable!("bucket index is in range"),
        }
    }

    // Fallback for each failed bucket: Bob sends the IDs he holds in that
    // bucket (about 1/16 of his set), and Alice compares them with hers.
    for &bucket in &failed_buckets {
        let in_bucket = |ids: &[u64]| -> BTreeSet<u64> {
            ids.iter()
                .copied()
                .filter(|&id| shape.bucket_for(id) == bucket)
                .collect()
        };
        let (alice_part, bob_part) = (in_bucket(&alice_ids), in_bucket(&bob_ids));
        println!(
            "bucket {bucket:2}: fallback exchanges {} IDs",
            bob_part.len()
        );
        recovered.extend(alice_part.symmetric_difference(&bob_part).copied());
    }

    assert_eq!(recovered, BTreeSet::from_iter(bob_only));
    println!("Recovered all {} differences", recovered.len());
    Ok(())
}
