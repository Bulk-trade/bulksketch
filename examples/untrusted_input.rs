//! Decoding sketches that arrive from peers you do not trust.
//!
//! Every input passes through limits that you choose: the parser rejects
//! messages that are too large or malformed, and the decoder stops a request
//! that would exceed its work budget. This example shows each check failing on
//! purpose, and how to pick a secret seed.
//!
//! Run it with:
//!
//! ```sh
//! cargo run --release --example untrusted_input
//! ```

use {
    bulksketch::{
        BackendRequest, DecodeError, DecodeLimits, DecodePlan, DecodeRequest, DecodeScratch,
        Decoder, FrozenSketch, Gf64, MutableSketch, ParseError, ParseLimits, ShapeLimits,
        SketchShape, SketchView, WorkUnits, decode_into,
    },
    std::{
        error::Error,
        hash::{BuildHasher, RandomState},
        sync::Arc,
    },
};

const CAPACITY: usize = 18;

fn sketch(capacity: usize, ids: &[u64]) -> Result<FrozenSketch<Gf64>, Box<dyn Error>> {
    let limits = ShapeLimits {
        max_wire_bytes: 4096,
        max_buckets: 1,
        max_capacity_per_bucket: 64,
        max_total_syndrome_words: 64,
    };
    let shape = Arc::new(SketchShape::new(&[capacity], &limits)?);
    let mut sketch = MutableSketch::new(shape, BackendRequest::Auto)?;
    for &id in ids {
        sketch.toggle(id);
    }
    Ok(sketch.freeze())
}

fn main() -> Result<(), Box<dyn Error>> {
    // A secret seed makes the decoder's internal choices unpredictable to an
    // attacker. Draw it from a random source once per process and keep it
    // private. The standard library has no public random number API;
    // `RandomState` is seeded from the operating system's random source, which
    // is enough here. Crates such as `getrandom` are the usual choice.
    let seed = RandomState::new().hash_one("bulksketch decoder seed");
    let decoder = Decoder::new(BackendRequest::Auto, seed)?;

    // The limits Alice accepts for incoming sketches: one bucket of capacity 18.
    let parse_limits = ParseLimits {
        max_wire_bytes: 4096,
        max_buckets: 1,
        max_capacity_per_bucket: CAPACITY,
        max_total_syndrome_words: CAPACITY,
    };

    let alice = sketch(CAPACITY, &[1, 2, 3])?;
    let honest = sketch(CAPACITY, &[1, 2, 4])?;
    let honest_bytes = honest.encoded_v1()?.to_vec();

    // 1. Malformed input: a cut-off message and random bytes are rejected
    //    before anything is allocated.
    let cut = &honest_bytes[..honest_bytes.len() - 1];
    assert_eq!(
        SketchView::<Gf64>::parse(cut, &parse_limits).err(),
        Some(ParseError::InvalidEncoding)
    );
    let noise = [0xa5u8; 64];
    assert_eq!(
        SketchView::<Gf64>::parse(&noise, &parse_limits).err(),
        Some(ParseError::InvalidEncoding)
    );
    println!("malformed messages: rejected (InvalidEncoding)");

    // 2. A well-formed sketch that is larger than Alice accepts.
    let too_big = sketch(64, &[1, 2, 4])?;
    assert_eq!(
        SketchView::<Gf64>::parse(too_big.encoded_v1()?, &parse_limits).err(),
        Some(ParseError::InputLimitExceeded)
    );
    println!("oversized sketch: rejected (InputLimitExceeded)");

    // Size the decode for any input of Alice's shape.
    let plan = DecodePlan::v3();
    let (max_work, layout) =
        plan.complete_bound(&[CAPACITY as u16], &[Some(CAPACITY)], CAPACITY, 0)?;
    let limits = DecodeLimits {
        max_output_per_bucket: CAPACITY,
        max_candidate_inputs: 0,
        max_work,
        max_scratch_bytes: layout.total_bytes(),
    };
    let mut scratch = DecodeScratch::new(&layout)?;

    // 3. A sketch with a different shape (capacity 17 instead of 18). It
    //    parses, because it is within the limits, but cannot be compared with
    //    Alice's sketch.
    let other_shape = sketch(17, &[1, 2, 4])?;
    let view = SketchView::parse(other_shape.encoded_v1()?, &parse_limits)?;
    let request = DecodeRequest {
        local: &alice,
        remote: view,
        candidates: &[],
        plan: &plan,
        limits: &limits,
    };
    assert_eq!(
        decode_into(request, &decoder, &mut scratch).err(),
        Some(DecodeError::ShapeMismatch)
    );
    println!("different shape: rejected (ShapeMismatch)");

    // 4. A work budget that is too small. The request stops as soon as the
    //    next step would exceed the budget, and returns no partial result.
    let view = SketchView::parse(&honest_bytes, &parse_limits)?;
    let tight = DecodeLimits {
        max_work: WorkUnits(10),
        ..limits
    };
    let request = DecodeRequest {
        local: &alice,
        remote: view,
        candidates: &[],
        plan: &plan,
        limits: &tight,
    };
    assert_eq!(
        decode_into(request, &decoder, &mut scratch).err(),
        Some(DecodeError::WorkLimitExceeded)
    );
    println!("work budget of 10 units: stopped (WorkLimitExceeded)");

    // The same honest sketch with the full budget decodes. The scratch memory
    // is reused; nothing is allocated during the decode.
    let request = DecodeRequest {
        local: &alice,
        remote: view,
        candidates: &[],
        plan: &plan,
        limits: &limits,
    };
    let report = decode_into(request, &decoder, &mut scratch)?;
    let outcome = report.outcome(0).expect("the shape has one bucket");
    println!("honest sketch: {outcome:?}, {} work units", report.work.0);
    Ok(())
}
