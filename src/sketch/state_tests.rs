#![forbid(unsafe_code)]

use {
    super::*,
    crate::{
        BackendId, BackendRequest, EncodeError, Gf64, ShapeMismatch, UpdateError, field::reference,
    },
    std::sync::Arc,
};

fn make_shape(capacities: &[usize]) -> Arc<SketchShape<Gf64>> {
    Arc::new(
        SketchShape::new(
            capacities,
            &ShapeLimits {
                max_wire_bytes: 100_000,
                max_buckets: 16,
                max_capacity_per_bucket: 89,
                max_total_syndrome_words: 1424,
            },
        )
        .unwrap(),
    )
}

fn empty(shape: &Arc<SketchShape<Gf64>>) -> MutableSketch<Gf64> {
    MutableSketch::new(
        Arc::clone(shape),
        BackendRequest::Force(BackendId::Portable),
    )
    .unwrap()
}

fn reconstruct(shape: &Arc<SketchShape<Gf64>>, ids: &[u64]) -> FrozenSketch<Gf64> {
    let mut sketch = empty(shape);
    for &id in ids {
        sketch.toggle(id);
    }
    sketch.freeze()
}

fn assert_same(actual: &FrozenSketch<Gf64>, expected: &FrozenSketch<Gf64>, message: &str) {
    assert_eq!(actual.state.words, expected.state.words, "{message}: words");
    assert_eq!(
        actual.state.zero_words, expected.state.zero_words,
        "{message}: zero"
    );
    assert_eq!(
        actual.encoded_v1().unwrap(),
        expected.encoded_v1().unwrap(),
        "{message}: bytes"
    );
}

#[test]
fn insertion_and_xor_algebra() {
    let ids = [0, 17, 1 << 63, 31, u64::MAX, 17, 3, 0, 9, 0, 7];
    for buckets in [1, 4, 16] {
        for capacity in [18, 72, 89] {
            let dimensions: Vec<_> = (0..buckets).map(|b| capacity - b % 3).collect();
            let shape = make_shape(&dimensions);
            let mut batch = empty(&shape);
            let mut scratch = InsertScratch::new(8, buckets).unwrap();
            let mut independent = vec![0; shape.total_syndrome_words()];
            let mut zero = false;
            for chunk in ids.chunks(8) {
                batch.toggle_batch(chunk, &mut scratch).unwrap();
                for _ in chunk.iter().filter(|&&id| id == 0) {
                    zero = !zero;
                }
                for &id in chunk.iter().filter(|&&id| id != 0) {
                    let bucket = usize::try_from(id % buckets as u64).unwrap();
                    let start: usize = dimensions[..bucket].iter().sum();
                    for (index, target) in independent[start..start + dimensions[bucket]]
                        .iter_mut()
                        .enumerate()
                    {
                        let mut power = 1;
                        for _ in 0..=2 * index {
                            power = reference::mul::<Gf64>(power, id);
                        }
                        *target ^= power;
                    }
                }
                assert_eq!(
                    batch.freeze().state.words,
                    independent,
                    "arrival chunks route identity words"
                );
                assert_eq!(
                    batch.freeze().state.zero_words[0],
                    u64::from(zero),
                    "zero arrivals toggle parity independently"
                );
            }
            let expected = reconstruct(&shape, &ids);
            assert_same(
                &batch.freeze(),
                &expected,
                "batch equals individual toggles",
            );
            let mut reverse = ids;
            reverse.reverse();
            assert_same(
                &reconstruct(&shape, &reverse),
                &expected,
                "permutation invariance",
            );
            let mut merged = empty(&shape);
            for half in ids.chunks(6) {
                merged.xor_assign(&reconstruct(&shape, half)).unwrap();
            }
            assert_same(&merged.freeze(), &expected, "linearity");
            batch.toggle_batch(&ids[..8], &mut scratch).unwrap();
            batch.toggle_batch(&ids[8..], &mut scratch).unwrap();
            assert_same(
                &batch.freeze(),
                &empty(&shape).freeze(),
                "double-toggle cancellation",
            );
        }
    }
}

#[test]
fn unique_cache_invalidates_every_mutation() {
    let shape = make_shape(&[3, 2, 4, 1]);
    let initial = [0, 1, 4, u64::MAX];
    for mutation in 0_usize..6 {
        let mut sketch = empty(&shape);
        for &id in &initial {
            sketch.toggle(id);
        }
        {
            let snapshot = sketch.freeze();
            assert!(!snapshot.encoded_v1().unwrap().is_empty());
        }
        let extra: &[u64] = if mutation.is_multiple_of(2) {
            &[0]
        } else {
            &[0, 8, 7]
        };
        match mutation / 2 {
            0 => {
                for &id in extra {
                    sketch.toggle(id);
                }
            }
            1 => sketch
                .toggle_batch(extra, &mut InsertScratch::new(extra.len(), 4).unwrap())
                .unwrap(),
            _ => sketch.xor_assign(&reconstruct(&shape, extra)).unwrap(),
        }
        let expected = reconstruct(&shape, &[initial.as_slice(), extra].concat());
        assert_same(&sketch.freeze(), &expected, "encode-drop-mutate-refreeze");
    }
}

#[test]
fn mutable_clones_and_thaws_are_isolated() {
    let shape = make_shape(&[3; 4]);
    let original = reconstruct(&shape, &[0, 1, 9, u64::MAX]);
    let sibling = original.clone();
    assert!(
        Arc::ptr_eq(&original.state, &sibling.state),
        "frozen clones share immutable state"
    );
    let before = original.encoded_v1().unwrap().to_vec();
    for reverse in [false, true] {
        let left = original.thaw(BackendRequest::Auto).unwrap();
        let mut clones = [left.clone(), left];
        for index in if reverse { [1, 0] } else { [0, 1] } {
            let id = 20 + index as u64;
            clones[index].toggle(id);
            let expected = reconstruct(&shape, &[0, 1, 9, u64::MAX, id]);
            assert_same(
                &clones[index].freeze(),
                &expected,
                "mutable clone owns its mutation",
            );
            assert_eq!(
                original.encoded_v1().unwrap(),
                before,
                "live snapshot cache survives sibling mutation"
            );
        }
        clones[0]
            .toggle_batch(&[0, 2], &mut InsertScratch::new(2, 4).unwrap())
            .unwrap();
        clones[1].xor_assign(&reconstruct(&shape, &[0, 3])).unwrap();
        assert_same(
            &clones[0].freeze(),
            &reconstruct(&shape, &[0, 1, 9, u64::MAX, 20, 0, 2]),
            "clone batch isolation",
        );
        assert_same(
            &clones[1].freeze(),
            &reconstruct(&shape, &[0, 1, 9, u64::MAX, 21, 0, 3]),
            "clone XOR isolation",
        );
    }
}

#[test]
fn failed_updates_preserve_cache_and_algebra() {
    let shape = make_shape(&[2; 4]);
    let snapshot = reconstruct(&shape, &[0, 1, 2]);
    let mut sketch = snapshot.thaw(BackendRequest::Auto).unwrap();
    let cached = snapshot.encoded_v1().unwrap().as_ptr();
    for mut scratch in [
        InsertScratch::new(0, 4).unwrap(),
        InsertScratch::new(8, 3).unwrap(),
    ] {
        assert_eq!(
            sketch.toggle_batch(&[0], &mut scratch),
            Err(UpdateError::ScratchTooSmall)
        );
        let frozen = sketch.freeze();
        assert_eq!(
            frozen.encoded_v1().unwrap().as_ptr(),
            cached,
            "failed batch retains cache cell"
        );
        assert_same(&frozen, &snapshot, "failed batch is transactional");
    }
    assert_eq!(
        sketch.xor_assign(&reconstruct(&make_shape(&[1; 4]), &[0])),
        Err(ShapeMismatch)
    );
    assert_same(
        &sketch.freeze(),
        &snapshot,
        "shape mismatch cannot truncate",
    );
    assert_eq!(
        sketch.freeze().encoded_v1().unwrap().as_ptr(),
        cached,
        "failed XOR retains cache cell"
    );
    let frozen = sketch.freeze();
    let mut short = vec![0x99; frozen.shape().wire_bytes() - 1];
    assert_eq!(
        frozen.encode_into(&mut short),
        Err(EncodeError::BufferTooSmall)
    );
    assert!(
        short.iter().all(|&b| b == 0x99),
        "short encoding performs no writes"
    );
}

#[test]
fn public_backend_requests_are_checked() {
    fn send_sync<T: Send + Sync>() {}
    let _unavailable = crate::backend::detect::without_vector();
    let shape = make_shape(&[1]);
    let frozen = empty(&shape).freeze();
    for id in [
        BackendId::Pclmul,
        BackendId::Vpclmul256,
        BackendId::Vpclmul512,
    ] {
        let request = BackendRequest::Force(id);
        assert_eq!(
            MutableSketch::new(Arc::clone(&shape), request).map(|_| ()),
            Err(crate::CreateError::Backend(crate::BackendError(id)))
        );
        assert_eq!(
            frozen.thaw(request).map(|_| ()),
            Err(crate::BackendError(id))
        );
        assert_eq!(
            Decoder::<Gf64>::new(request, 1).map(|_| ()),
            Err(crate::BackendError(id)),
            "public decoder cannot bypass built backend checks"
        );
    }
    for request in [
        BackendRequest::Auto,
        BackendRequest::Force(BackendId::Portable),
    ] {
        assert!(MutableSketch::new(Arc::clone(&shape), request).is_ok());
        assert!(frozen.thaw(request).is_ok());
        assert!(Decoder::<Gf64>::new(request, 1).is_ok());
    }
    send_sync::<MutableSketch<Gf64>>();
    send_sync::<FrozenSketch<Gf64>>();
    send_sync::<Decoder<Gf64>>();
    send_sync::<DecodeScratch<Gf64>>();
    send_sync::<InsertScratch>();
    assert_eq!(
        InsertScratch::new(usize::MAX, 1).unwrap_err(),
        UpdateError::ScratchTooSmall
    );
    assert_eq!(
        InsertScratch::new(1, usize::MAX).unwrap_err(),
        UpdateError::ScratchTooSmall
    );
}
