//! Borrowed independent rows share the ordinary staged request driver.
#![forbid(unsafe_code)]

use {
    super::{
        api::{DecodeLimits, DecodeRequest},
        candidates,
        plan::DecodePlan,
        shape::SketchShape,
        state::{FrozenSketch, State},
    },
    crate::{field::BinaryField, types::DecodeError},
    std::sync::Arc,
};

/// One independent, nonzero-only GF64 row. Payload words are little-endian and
/// may be unaligned. No framing is copied or synthesized during decoding.
#[derive(Clone, Copy, Debug)]
pub struct DecodeRow<'a, F: BinaryField> {
    /// Immutable local sketch, which must have exactly one row.
    pub local: &'a FrozenSketch<F>,
    /// Exactly eight bytes per local odd syndrome; no zero-membership channel.
    pub remote: &'a [u8],
    /// Hints for this row only, before zero removal or deduplication.
    pub candidates: &'a [u64],
}

/// One request over independently routed rows, in caller order. IDs are checked
/// against each local one-row shape, rather than against the batch row count.
/// A request error suppresses every result; an algebraic failure affects one row.
#[derive(Clone, Copy, Debug)]
pub struct DecodeRowsRequest<'a, F: BinaryField> {
    /// Nonempty borrowed rows. Each remote row has implicit zero membership false.
    pub rows: &'a [DecodeRow<'a, F>],
    /// Explicit algorithm and charge schedule, shared by all rows.
    pub plan: &'a DecodePlan,
    /// Aggregate request limits; the output budget still applies to each row.
    pub limits: &'a DecodeLimits,
}

// The two entry points share one driver, specialized at compile time. A native
// request must not carry a borrowed-row discriminator through every row/stage.
pub trait RequestInput<F: BinaryField> {
    fn plan(&self) -> &DecodePlan;
    fn limits(&self) -> &DecodeLimits;
    fn bucket_count(&self) -> usize;
    fn capacity(&self, bucket: usize) -> usize;
    fn validate_shape(&self) -> Result<(), DecodeError>;
    fn candidate_count(&self) -> Result<usize, DecodeError>;
    fn zero(&self, bucket: usize) -> bool;
    fn remaining_rows(
        &self,
        bucket: usize,
        word_offset: usize,
    ) -> impl Iterator<Item = (usize, InputRow<'_, F>)>;
    fn normalize(&self, storage: &mut [u64]);
    fn permits_id(&self, bucket: usize, id: u64) -> bool;
    fn cached_shape(&self, beta: usize) -> Option<&Arc<SketchShape<F>>>;
}

pub struct InputRow<'a, F: BinaryField> {
    pub(super) local: &'a State<F>,
    pub(super) word_offset: usize,
    pub(super) remote: &'a [u8],
    pub(super) zero: bool,
}

impl<F: BinaryField> RequestInput<F> for DecodeRequest<'_, F> {
    fn plan(&self) -> &DecodePlan {
        self.plan
    }
    fn limits(&self) -> &DecodeLimits {
        self.limits
    }
    fn bucket_count(&self) -> usize {
        self.local.shape().bucket_count()
    }
    fn capacity(&self, bucket: usize) -> usize {
        usize::from(self.local.shape().capacities()[bucket])
    }
    fn validate_shape(&self) -> Result<(), DecodeError> {
        if self.local.shape().bucket_count() == self.remote.bucket_count()
            && self
                .local
                .shape()
                .capacities()
                .iter()
                .enumerate()
                .all(|(b, &c)| Some(usize::from(c)) == self.remote.capacity(b))
        {
            Ok(())
        } else {
            Err(DecodeError::ShapeMismatch)
        }
    }
    fn candidate_count(&self) -> Result<usize, DecodeError> {
        Ok(self.candidates.len())
    }
    fn zero(&self, bucket: usize) -> bool {
        bucket == 0
            && (self.local.state.zero_words[0] & 1 != 0)
                != self.remote.zero(0).expect("admitted row zero")
    }
    #[inline(always)]
    fn remaining_rows(
        &self,
        bucket: usize,
        mut word_offset: usize,
    ) -> impl Iterator<Item = (usize, InputRow<'_, F>)> {
        let local = self.local.state.as_ref();
        let remote = self.remote.syndrome_bytes();
        let mut zero = bucket == 0 && self.zero(0);
        local.shape.capacities()[bucket..]
            .iter()
            .map(move |&capacity| {
                let capacity = usize::from(capacity);
                let start = word_offset;
                word_offset += capacity;
                let row = InputRow {
                    local,
                    word_offset: start,
                    remote: &remote[8 * start..8 * word_offset],
                    zero,
                };
                zero = false;
                (capacity, row)
            })
    }
    fn normalize(&self, storage: &mut [u64]) {
        candidates::normalize(self.local.shape(), self.candidates, storage);
    }
    fn permits_id(&self, bucket: usize, id: u64) -> bool {
        self.local.shape().permits_id(bucket, id)
    }
    fn cached_shape(&self, _beta: usize) -> Option<&Arc<SketchShape<F>>> {
        (!self.zero(0)).then_some(&self.local.state.shape)
    }
}

impl<F: BinaryField> RequestInput<F> for DecodeRowsRequest<'_, F> {
    fn plan(&self) -> &DecodePlan {
        self.plan
    }
    fn limits(&self) -> &DecodeLimits {
        self.limits
    }
    fn bucket_count(&self) -> usize {
        self.rows.len()
    }
    fn capacity(&self, bucket: usize) -> usize {
        usize::from(self.rows[bucket].local.shape().capacities()[0])
    }
    fn validate_shape(&self) -> Result<(), DecodeError> {
        if !self.rows.is_empty()
            && self.rows.iter().all(|row| {
                row.local.shape().bucket_count() == 1
                    && row.remote.len() == 8 * row.local.shape().total_syndrome_words()
            })
        {
            Ok(())
        } else {
            Err(DecodeError::ShapeMismatch)
        }
    }
    fn candidate_count(&self) -> Result<usize, DecodeError> {
        self.rows.iter().try_fold(0usize, |n, row| {
            n.checked_add(row.candidates.len())
                .ok_or(DecodeError::WorkLimitExceeded)
        })
    }
    fn zero(&self, bucket: usize) -> bool {
        self.rows[bucket].local.state.zero_words[0] & 1 != 0
    }
    #[inline(always)]
    fn remaining_rows(
        &self,
        bucket: usize,
        _word_offset: usize,
    ) -> impl Iterator<Item = (usize, InputRow<'_, F>)> {
        self.rows[bucket..].iter().map(|row| {
            let local = row.local.state.as_ref();
            (
                usize::from(local.shape.capacities()[0]),
                InputRow {
                    local,
                    word_offset: 0,
                    remote: row.remote,
                    zero: local.zero_words[0] & 1 != 0,
                },
            )
        })
    }
    fn normalize(&self, storage: &mut [u64]) {
        candidates::normalize_rows(self.rows, storage);
    }
    fn permits_id(&self, bucket: usize, id: u64) -> bool {
        self.rows[bucket].local.shape().permits_id(0, id)
    }
    fn cached_shape(&self, beta: usize) -> Option<&Arc<SketchShape<F>>> {
        (0..self.rows.len())
            .all(|b| self.capacity(b) == beta && !self.zero(b))
            .then_some(&self.rows[0].local.state.shape)
    }
}
