//! The usage example from README.md, kept compiling and passing.
use {
    bulksketch::{
        BackendRequest, DecodeLimits, DecodeOutcome, DecodePlan, DecodeRequest, DecodeScratch,
        Decoder, Gf64, MutableSketch, ParseLimits, ShapeLimits, SketchShape, SketchView,
        decode_into,
    },
    std::sync::Arc,
};

#[test]
fn readme_example() {
    // One bucket of capacity 18: up to 18 differences can be recovered.
    let capacity = 18;
    let shape = Arc::new(
        SketchShape::<Gf64>::new(
            &[capacity],
            &ShapeLimits {
                max_wire_bytes: 1024,
                max_buckets: 1,
                max_capacity_per_bucket: capacity,
                max_total_syndrome_words: capacity,
            },
        )
        .unwrap(),
    );

    // Each side adds its IDs (nonzero u64 hashes) to its own sketch.
    let mut alice = MutableSketch::new(shape.clone(), BackendRequest::Auto).unwrap();
    let mut bob = MutableSketch::new(shape, BackendRequest::Auto).unwrap();
    for id in [11, 22, 33, 44] {
        alice.toggle(id);
    }
    for id in [11, 22, 55] {
        bob.toggle(id);
    }
    let alice = alice.freeze();
    let bob = bob.freeze();

    // Bob sends his encoded sketch; Alice parses it under her own limits.
    let wire = bob.encoded_v1().unwrap();
    let remote = SketchView::parse(
        wire,
        &ParseLimits {
            max_wire_bytes: 1024,
            max_buckets: 1,
            max_capacity_per_bucket: capacity,
            max_total_syndrome_words: capacity,
        },
    )
    .unwrap();

    // The plan computes a work budget and a scratch size that cover any input.
    let plan = DecodePlan::v3();
    let (max_work, layout) = plan
        .complete_bound(&[capacity as u16], &[Some(capacity)], capacity, 0)
        .unwrap();
    let limits = DecodeLimits {
        max_output_per_bucket: capacity,
        max_candidate_inputs: 0,
        max_work,
        max_scratch_bytes: layout.total_bytes(),
    };
    // Use a secret splitter seed in production, a fixed one in tests and simulations.
    let decoder = Decoder::new(BackendRequest::Auto, 0x1234_5678).unwrap();
    let mut scratch = DecodeScratch::new(&layout).unwrap();

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
    )
    .unwrap();
    // The symmetric difference, ascending and verified against every syndrome.
    assert_eq!(
        report.outcome(0),
        Some(DecodeOutcome::Decoded { ids: &[33, 44, 55] })
    );
}
