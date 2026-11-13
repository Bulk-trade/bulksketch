//! Running a decode one stage at a time with `DecodeJob`.
//!
//! `decode_into` runs a whole request in one call. A `DecodeJob` runs the same
//! request in small steps, so a caller can interleave decoding with other work
//! (for example, one stage per event-loop turn) and watch the work used so far.
//! The steps and the result are deterministic: the same inputs and seed always
//! give the same stages, work counts and output.
//!
//! Run it with:
//!
//! ```sh
//! cargo run --release --example staged
//! ```

use {
    bulksketch::{
        BackendRequest, DecodeJob, DecodeLimits, DecodePlan, DecodeRequest, DecodeScratch, Decoder,
        Gf64, MutableSketch, ParseLimits, ShapeLimits, SketchShape, SketchView, StageProgress,
    },
    std::{error::Error, sync::Arc},
};

const BUCKETS: usize = 2;
const CAPACITY: usize = 18;

fn main() -> Result<(), Box<dyn Error>> {
    let shape = Arc::new(SketchShape::<Gf64>::new(
        &[CAPACITY; BUCKETS],
        &ShapeLimits {
            max_wire_bytes: 4096,
            max_buckets: BUCKETS,
            max_capacity_per_bucket: CAPACITY,
            max_total_syndrome_words: BUCKETS * CAPACITY,
        },
    )?);

    // Alice's sketch is empty. Bob's holds one ID in bucket 0 and six IDs in
    // bucket 1 (an ID goes to bucket `id % 2`).
    let alice = MutableSketch::new(Arc::clone(&shape), BackendRequest::Auto)?;
    // Cloning is cheap: the clone shares Alice's state until it is changed.
    let mut bob = alice.clone();
    for id in [10, 1001, 2003, 3005, 4007, 5009, 6011] {
        bob.toggle(id);
    }
    let (alice, bob) = (alice.freeze(), bob.freeze());

    let message = bob.encoded_v1()?.to_vec();
    let remote = SketchView::parse(
        &message,
        &ParseLimits {
            max_wire_bytes: 4096,
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

    // `new` checks the whole request (shapes, plan, limits, scratch size)
    // before any decoding starts.
    let mut job = DecodeJob::new(
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

    // Run one stage per loop turn. Progress reports which bucket and stage ran
    // and the work used so far, but never partial results.
    while job.next_stage().is_some() {
        match job.run_next() {
            StageProgress::Completed {
                bucket,
                stage,
                work,
                ..
            } => {
                println!("bucket {bucket}: {stage:?} done, work so far {}", work.0);
            }
            StageProgress::Failed(error) => {
                // A request-wide failure, such as running out of work budget.
                // `finish` returns the same error.
                println!("request failed: {error}");
                break;
            }
        }
    }

    // `finish` runs any remaining stages and returns the report.
    let report = job.finish()?;
    for bucket in 0..report.bucket_count() {
        let outcome = report.outcome(bucket).expect("bucket index is in range");
        println!("bucket {bucket}: {outcome:?}");
    }
    Ok(())
}
