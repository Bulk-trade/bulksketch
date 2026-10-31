#![forbid(unsafe_code)]

use {
    bulksketch::{
        BackendId, BackendRequest, Gf64, InsertScratch, MutableSketch, ShapeLimits, SketchShape,
    },
    std::sync::Arc,
};

fn mix(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

#[test]
fn single_insert_all_words_and_generations() {
    // Exercise the public single-ID caller, including nonempty rows, live
    // snapshots and a populated encoding cache. The reference uses Portable's
    // separate batch caller so a single-ID routing defect cannot poison both.
    for capacity in 1..=100 {
        let shape = Arc::new(
            SketchShape::<Gf64>::new(
                &[capacity],
                &ShapeLimits {
                    max_wire_bytes: 4096,
                    max_buckets: 1,
                    max_capacity_per_bucket: 100,
                    max_total_syndrome_words: 100,
                },
            )
            .unwrap(),
        );
        let Ok(mut actual) = MutableSketch::new(
            Arc::clone(&shape),
            BackendRequest::Force(BackendId::Vpclmul512),
        ) else {
            return;
        };
        let mut expected =
            MutableSketch::new(shape, BackendRequest::Force(BackendId::Portable)).unwrap();
        let mut scratch = InsertScratch::new(1, 1).unwrap();
        let ids = [0, 1, u64::MAX, 0xaaaa_aaaa_aaaa_aaaa, 0x5555_5555_5555_5555]
            .into_iter()
            .chain((0..64).map(|bit| 1_u64 << bit))
            .chain((0..64).map(mix));
        for id in ids {
            let snapshot = actual.freeze();
            let saved = snapshot.encoded_v1().unwrap().to_vec();
            for _ in 0..2 {
                actual.toggle(id);
                expected.toggle_batch(&[id], &mut scratch).unwrap();
                assert_eq!(
                    actual.freeze().encoded_v1().unwrap(),
                    expected.freeze().encoded_v1().unwrap(),
                    "single-ID c={capacity} id={id:#018x}"
                );
                assert_eq!(snapshot.encoded_v1().unwrap(), saved, "snapshot changed");
            }
            // Leave a nonempty generation for the next ID, then invalidate its
            // already populated cache through the same single-ID caller.
            actual.toggle(id);
            expected.toggle_batch(&[id], &mut scratch).unwrap();
        }
    }
}
