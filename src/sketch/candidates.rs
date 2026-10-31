//! Bounded, allocation-free normalization into row-major nonzero identity hints.
#![forbid(unsafe_code)]

use {super::shape::SketchShape, crate::field::BinaryField};

pub(super) fn normalize<F: BinaryField>(
    shape: &SketchShape<F>,
    inputs: &[u64],
    storage: &mut [u64],
) {
    if inputs.is_empty() {
        storage.fill(0);
        return;
    }
    let count = inputs.len();
    let (arrays, offsets) = storage.split_at_mut(2 * count);
    let (mut ids, mut temporary) = arrays.split_at_mut(count);
    ids.copy_from_slice(inputs);
    let key = |id| (shape.bucket_for(id), id);
    let mut width = 1;
    let mut flipped = false;
    while width < count {
        let mut start = 0;
        while start < count {
            let middle = start + width.min(count - start);
            let end = middle + width.min(count - middle);
            let (mut left, mut right) = (start, middle);
            for target in &mut temporary[start..end] {
                if left < middle && (right == end || key(ids[left]) <= key(ids[right])) {
                    *target = ids[left];
                    left += 1;
                } else {
                    *target = ids[right];
                    right += 1;
                }
            }
            start = end;
        }
        std::mem::swap(&mut ids, &mut temporary);
        flipped = !flipped;
        if width >= count - width {
            break;
        }
        width *= 2;
    }
    if flipped {
        temporary.copy_from_slice(ids);
        std::mem::swap(&mut ids, &mut temporary);
    }
    offsets.fill(0);
    let mut used = 0;
    for index in 0..count {
        let id = ids[index];
        if id != 0 && (used == 0 || ids[used - 1] != id) {
            ids[used] = id;
            used += 1;
            offsets[shape.bucket_for(id) + 1] += 1;
        }
    }
    for bucket in 0..shape.bucket_count() {
        offsets[bucket + 1] += offsets[bucket];
    }
}

pub(super) fn row(storage: &[u64], raw_count: usize, bucket: usize) -> &[u64] {
    if raw_count == 0 {
        return &storage[..0];
    }
    let offsets = &storage[2 * raw_count..];
    let start = usize::try_from(offsets[bucket]).expect("admitted candidate offset");
    let end = usize::try_from(offsets[bucket + 1]).expect("admitted candidate offset");
    &storage[start..end]
}

/// Row-local normalization: repeats in different rows remain separate hints.
pub(super) fn normalize_rows<F: BinaryField>(
    rows: &[super::input::DecodeRow<'_, F>],
    storage: &mut [u64],
) {
    let count: usize = rows.iter().map(|row| row.candidates.len()).sum();
    if count == 0 {
        storage.fill(0);
        return;
    }
    let (arrays, offsets) = storage.split_at_mut(2 * count);
    let (ids, _) = arrays.split_at_mut(count);
    offsets.fill(0);
    let mut used = 0;
    for (bucket, row) in rows.iter().enumerate() {
        let start = used;
        ids[start..start + row.candidates.len()].copy_from_slice(row.candidates);
        ids[start..start + row.candidates.len()].sort_unstable();
        for index in start..start + row.candidates.len() {
            let id = ids[index];
            if id != 0 && (used == start || ids[used - 1] != id) {
                ids[used] = id;
                used += 1;
            }
        }
        offsets[bucket + 1] = used as u64;
    }
}
