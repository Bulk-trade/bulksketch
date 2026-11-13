//! Two peers find the IDs they do not have in common by exchanging one small
//! sketch instead of their full ID lists.
//!
//! Run it with:
//!
//! ```sh
//! cargo run --release --example reconcile
//! ```

use {
    bulksketch::{
        BackendRequest, DecodeLimits, DecodeOutcome, DecodePlan, DecodeRequest, DecodeScratch,
        Decoder, Gf64, MutableSketch, ParseLimits, ShapeLimits, SketchShape, SketchView,
        decode_into,
    },
    std::{collections::BTreeSet, error::Error, sync::Arc},
};

/// Up to this many differences can be recovered from one sketch.
const CAPACITY: usize = 18;

/// Stand-in for real 64-bit IDs such as hashes: multiplying by an odd constant
/// spreads consecutive numbers over the whole `u64` range without collisions.
fn id(n: u64) -> u64 {
    n.wrapping_mul(0x9e37_79b9_7f4a_7c15)
}

fn main() -> Result<(), Box<dyn Error>> {
    // Both peers hold 10,000 IDs in common. Alice has three that Bob lacks, and
    // Bob has two that Alice lacks.
    let common: Vec<u64> = (1..=10_000).map(id).collect();
    let alice_only = [id(20_001), id(20_002), id(20_003)];
    let bob_only = [id(30_001), id(30_002)];
    let alice_set: BTreeSet<u64> = common.iter().chain(&alice_only).copied().collect();
    let bob_set: BTreeSet<u64> = common.iter().chain(&bob_only).copied().collect();

    // Both peers must use the same shape. Here it is one bucket of capacity 18.
    // The limits cap how much memory a shape may take; there is no unbounded default.
    let shape_limits = ShapeLimits {
        max_wire_bytes: 4096,
        max_buckets: 1,
        max_capacity_per_bucket: CAPACITY,
        max_total_syndrome_words: CAPACITY,
    };
    let shape = Arc::new(SketchShape::<Gf64>::new(&[CAPACITY], &shape_limits)?);

    // Each peer adds its IDs to its own sketch, then freezes it into an
    // immutable snapshot.
    let mut alice = MutableSketch::new(Arc::clone(&shape), BackendRequest::Auto)?;
    for &id in &alice_set {
        alice.toggle(id);
    }
    let alice = alice.freeze();

    let mut bob = MutableSketch::new(shape, BackendRequest::Auto)?;
    for &id in &bob_set {
        bob.toggle(id);
    }
    let bob = bob.freeze();

    // Bob sends his encoded sketch. Its size depends on the capacity, not on
    // how many IDs Bob holds.
    let message: Vec<u8> = bob.encoded_v1()?.to_vec();
    println!(
        "Bob sends {} bytes instead of {} bytes of IDs",
        message.len(),
        bob_set.len() * 8
    );

    // Alice treats the message as untrusted input and parses it under her own limits.
    let parse_limits = ParseLimits {
        max_wire_bytes: 4096,
        max_buckets: 1,
        max_capacity_per_bucket: CAPACITY,
        max_total_syndrome_words: CAPACITY,
    };
    let remote = SketchView::parse(&message, &parse_limits)?;

    // Size the decode. `complete_bound` returns a work budget and a scratch
    // layout that are enough for any input of this shape.
    let plan = DecodePlan::v3();
    let (max_work, layout) =
        plan.complete_bound(&[CAPACITY as u16], &[Some(CAPACITY)], CAPACITY, 0)?;
    let limits = DecodeLimits {
        max_output_per_bucket: CAPACITY,
        max_candidate_inputs: 0,
        max_work,
        max_scratch_bytes: layout.total_bytes(),
    };

    // The decoder and the scratch memory are created once and reused for every
    // decode. Use a secret random seed in production (see `untrusted_input.rs`);
    // a fixed seed keeps this example reproducible.
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

    // The decoded IDs are the symmetric difference: IDs that exactly one of the
    // two peers holds. Alice tells the two sides apart by checking her own set.
    match report.outcome(0) {
        Some(DecodeOutcome::Decoded { ids }) => {
            let (bob_lacks, alice_lacks): (Vec<u64>, Vec<u64>) =
                ids.iter().partition(|&&id| alice_set.contains(&id));
            println!("Bob lacks   {bob_lacks:x?}");
            println!("Alice lacks {alice_lacks:x?}");
            assert_eq!(BTreeSet::from_iter(bob_lacks), BTreeSet::from(alice_only));
            assert_eq!(BTreeSet::from_iter(alice_lacks), BTreeSet::from(bob_only));
        }
        // Equal sketches. Within the capacity, that means equal sets.
        Some(DecodeOutcome::Equal) => println!("The two sketches are equal"),
        Some(DecodeOutcome::Failed { reason }) => {
            // No verified result, most often because the sets differ in more
            // IDs than the capacity. Retry with a larger capacity or fall back
            // to exchanging the IDs themselves.
            println!("Could not decode: {reason:?}");
        }
        None => unreachable!("the shape has one bucket"),
    }
    println!("Work used: {} of {} units", report.work.0, max_work.0);
    Ok(())
}
