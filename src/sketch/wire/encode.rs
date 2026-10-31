//! Canonical GF64 framing; algebraic state contains no backend identity.
#![forbid(unsafe_code)]

use crate::{
    field::BinaryField,
    sketch::shape::SketchShape,
    types::{EncodeError, FieldId},
};

pub(crate) fn encode_into<F: BinaryField>(
    shape: &SketchShape<F>,
    words: &[u64],
    zero: &[u64],
    dst: &mut [u8],
) -> Result<usize, EncodeError> {
    let len = shape.wire_bytes();
    if dst.len() < len {
        return Err(EncodeError::BufferTooSmall);
    }
    let dst = &mut dst[..len];
    let buckets = shape.bucket_count();
    let descriptor_len = 2 * buckets;
    let payload_start = 24 + descriptor_len;
    dst[..24].fill(0);
    dst[..4].copy_from_slice(b"SKNC");
    dst[4] = 1;
    dst[5] = FieldId::Gf64 as u8;
    dst[6] = 1;
    dst[8..10].copy_from_slice(
        &u16::try_from(buckets)
            .expect("admitted bucket count")
            .to_le_bytes(),
    );
    dst[12..16].copy_from_slice(
        &u32::try_from(descriptor_len)
            .expect("admitted descriptors")
            .to_le_bytes(),
    );
    dst[16..20].copy_from_slice(
        &u32::try_from(len - payload_start)
            .expect("admitted payload")
            .to_le_bytes(),
    );
    for (target, capacity) in dst[24..payload_start]
        .chunks_exact_mut(2)
        .zip(shape.capacities())
    {
        target.copy_from_slice(&capacity.to_le_bytes());
    }
    let syndrome_start = payload_start + buckets.div_ceil(8);
    dst[payload_start..syndrome_start].fill(0);
    dst[payload_start] = u8::from(zero[0] & 1 != 0);
    for (target, word) in dst[syndrome_start..].chunks_exact_mut(8).zip(words) {
        target.copy_from_slice(&word.to_le_bytes());
    }
    Ok(len)
}
