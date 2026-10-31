//! Fixed identity/modulo mapping with checked storage admission.
#![forbid(unsafe_code)]

use {
    crate::{
        field::BinaryField,
        types::{FieldId, ShapeError},
    },
    std::marker::PhantomData,
};

/// Explicit allocation caps. There is deliberately no unbounded default.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ShapeLimits {
    /// Maximum complete `CoreWireV1` record size, including framing.
    pub max_wire_bytes: usize,
    /// Maximum number of rows.
    pub max_buckets: usize,
    /// Maximum odd-syndrome words per row.
    pub max_capacity_per_bucket: usize,
    /// Maximum aggregate odd-syndrome words.
    pub max_total_syndrome_words: usize,
}

/// Validated power-of-two GF64 row layout. All original u64 IDs are permitted.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SketchShape<F: BinaryField> {
    capacities: Box<[u16]>,
    total_words: usize,
    wire_bytes: usize,
    field: PhantomData<F>,
}

impl<F: BinaryField> SketchShape<F> {
    /// Admit dimensions and storage before allocating the capacity descriptors.
    ///
    /// # Errors
    /// Rejects invalid mapping dimensions or exceeded caller/wire limits.
    ///
    /// # Panics
    /// Only if an internal capacity-admission invariant is broken.
    pub fn new(capacities: &[usize], limits: &ShapeLimits) -> Result<Self, ShapeError> {
        if F::BITS != 64 || F::WIRE_ID != FieldId::Gf64 || !capacities.len().is_power_of_two() {
            return Err(ShapeError::InvalidShape);
        }
        if capacities.len() > limits.max_buckets || capacities.len() > usize::from(u16::MAX) {
            return Err(ShapeError::InputLimitExceeded);
        }
        let mut total_words = 0usize;
        for &capacity in capacities {
            if capacity > limits.max_capacity_per_bucket || capacity > usize::from(u16::MAX) {
                return Err(ShapeError::InputLimitExceeded);
            }
            total_words = total_words
                .checked_add(capacity)
                .ok_or(ShapeError::InputLimitExceeded)?;
            if total_words > limits.max_total_syndrome_words {
                return Err(ShapeError::InputLimitExceeded);
            }
        }
        if capacities.contains(&0) {
            return Err(ShapeError::InvalidShape);
        }
        let wire_bytes =
            record_bytes(capacities.len(), total_words).ok_or(ShapeError::InputLimitExceeded)?;
        if wire_bytes > limits.max_wire_bytes {
            return Err(ShapeError::InputLimitExceeded);
        }
        Ok(Self {
            capacities: capacities
                .iter()
                .map(|&c| u16::try_from(c).expect("admitted capacity"))
                .collect(),
            total_words,
            wire_bytes,
            field: PhantomData,
        })
    }

    /// Row capacities in bucket order.
    #[must_use]
    pub fn capacities(&self) -> &[u16] {
        &self.capacities
    }

    /// Row count, including empty-membership rows.
    #[must_use]
    pub fn bucket_count(&self) -> usize {
        self.capacities.len()
    }

    /// Aggregate number of stored odd syndromes.
    #[must_use]
    pub fn total_syndrome_words(&self) -> usize {
        self.total_words
    }

    /// Exact complete `CoreWireV1` record length.
    #[must_use]
    pub fn wire_bytes(&self) -> usize {
        self.wire_bytes
    }

    /// Total modulo routing; the field value is exactly `id`.
    ///
    /// # Panics
    /// Only if the previously validated shape is internally inconsistent.
    #[must_use]
    pub fn bucket_for(&self, id: u64) -> usize {
        usize::try_from(id % self.bucket_count() as u64).expect("remainder fits row count")
    }

    /// Validate an original ID recovered from the given row. Zero belongs only to row 0.
    #[must_use]
    pub fn permits_id(&self, bucket: usize, id: u64) -> bool {
        bucket < self.bucket_count() && self.bucket_for(id) == bucket
    }
}

pub(super) fn record_bytes(buckets: usize, words: usize) -> Option<usize> {
    let descriptors = buckets.checked_mul(2)?;
    let zero_bytes = buckets.checked_add(7)?.checked_div(8)?;
    let payload = words.checked_mul(8)?.checked_add(zero_bytes)?;
    u32::try_from(descriptors).ok()?;
    u32::try_from(payload).ok()?;
    24usize.checked_add(descriptors)?.checked_add(payload)
}
