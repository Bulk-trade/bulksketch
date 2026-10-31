//! Experimental `CoreWireV1`: SKNC, version/field/identity = 1/1/1.
#![forbid(unsafe_code)]

pub(crate) mod encode;

use {
    crate::{
        field::BinaryField,
        types::{FieldId, ParseError},
    },
    std::marker::PhantomData,
};

/// Explicit untrusted-input caps; no unbounded default is provided.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ParseLimits {
    /// Maximum complete input slice size.
    pub max_wire_bytes: usize,
    /// Maximum row count.
    pub max_buckets: usize,
    /// Maximum capacity in any row.
    pub max_capacity_per_bucket: usize,
    /// Maximum sum of row capacities.
    pub max_total_syndrome_words: usize,
}

/// Borrowed, completely validated GF64 identity representation. Parsing never allocates.
#[derive(Clone, Copy, Debug)]
pub struct SketchView<'a, F: BinaryField> {
    bytes: &'a [u8],
    buckets: usize,
    words: usize,
    payload_start: usize,
    field: PhantomData<F>,
}

impl<'a, F: BinaryField> SketchView<'a, F> {
    /// Validate bytes, fixed metadata/framing, dimension caps, then payload canonicality.
    ///
    /// # Errors
    /// Returns `InputLimitExceeded` or `InvalidEncoding` in a fixed order: size limit, then framing, then dimension caps, then payload canonicality.
    pub fn parse(bytes: &'a [u8], limits: &ParseLimits) -> Result<Self, ParseError> {
        use ParseError::{InputLimitExceeded, InvalidEncoding};
        if bytes.len() > limits.max_wire_bytes {
            return Err(InputLimitExceeded);
        }
        if bytes.len() < 24
            || &bytes[..4] != b"SKNC"
            || bytes[4] != 1
            || bytes[5] != FieldId::Gf64 as u8
            || bytes[6] != 1
            || bytes[7] != 0
            || bytes[10..12] != [0; 2]
            || bytes[20..24] != [0; 4]
            || F::BITS != 64
            || F::WIRE_ID != FieldId::Gf64
        {
            return Err(InvalidEncoding);
        }
        let buckets = usize::from(u16::from_le_bytes([bytes[8], bytes[9]]));
        if !buckets.is_power_of_two() {
            return Err(InvalidEncoding);
        }
        let descriptor_len = read_u32(bytes, 12)?;
        let payload_len = read_u32(bytes, 16)?;
        let payload_start = 24usize.checked_add(descriptor_len).ok_or(InvalidEncoding)?;
        if descriptor_len != buckets.checked_mul(2).ok_or(InvalidEncoding)?
            || payload_start.checked_add(payload_len) != Some(bytes.len())
        {
            return Err(InvalidEncoding);
        }
        if buckets > limits.max_buckets {
            return Err(InputLimitExceeded);
        }
        let mut words = 0usize;
        for descriptor in bytes[24..payload_start].chunks_exact(2) {
            let capacity = usize::from(u16::from_le_bytes([descriptor[0], descriptor[1]]));
            if capacity > limits.max_capacity_per_bucket {
                return Err(InputLimitExceeded);
            }
            words = words.checked_add(capacity).ok_or(InvalidEncoding)?;
            if words > limits.max_total_syndrome_words {
                return Err(InputLimitExceeded);
            }
        }
        let zero_bytes = buckets.checked_add(7).ok_or(InvalidEncoding)? / 8;
        if words.checked_mul(8).and_then(|n| n.checked_add(zero_bytes)) != Some(payload_len)
            || bytes[24..payload_start]
                .chunks_exact(2)
                .any(|c| c == [0, 0])
        {
            return Err(InvalidEncoding);
        }
        let zero = &bytes[payload_start..payload_start + zero_bytes];
        if zero[0] & !1 != 0 || zero[1..].iter().any(|&b| b != 0) {
            return Err(InvalidEncoding);
        }
        Ok(Self {
            bytes,
            buckets,
            words,
            payload_start,
            field: PhantomData,
        })
    }

    /// Original canonical encoding.
    #[must_use]
    pub fn as_bytes(&self) -> &'a [u8] {
        self.bytes
    }

    pub(crate) fn syndrome_bytes(&self) -> &'a [u8] {
        &self.bytes[self.payload_start + self.buckets.div_ceil(8)..]
    }

    /// Number of rows.
    #[must_use]
    pub fn bucket_count(&self) -> usize {
        self.buckets
    }

    /// Aggregate odd-syndrome count.
    #[must_use]
    pub fn total_syndrome_words(&self) -> usize {
        self.words
    }

    /// Capacity of a row, or `None` outside the admitted shape.
    #[must_use]
    pub fn capacity(&self, bucket: usize) -> Option<usize> {
        if bucket >= self.buckets {
            return None;
        }
        let offset = 24 + 2 * bucket;
        Some(usize::from(u16::from_le_bytes([
            self.bytes[offset],
            self.bytes[offset + 1],
        ])))
    }

    /// Zero membership; only row zero can carry it.
    #[must_use]
    pub fn zero(&self, bucket: usize) -> Option<bool> {
        (bucket < self.buckets).then(|| bucket == 0 && self.bytes[self.payload_start] & 1 != 0)
    }

    /// Read a canonical odd-syndrome word without assuming byte alignment.
    ///
    /// # Panics
    /// Only if parser-admitted offsets or dimensions are internally inconsistent.
    /// Out-of-range indices return `None`.
    #[must_use]
    pub fn odd_syndrome(&self, bucket: usize, index: usize) -> Option<u64> {
        if index >= self.capacity(bucket)? {
            return None;
        }
        let prior: usize = (0..bucket)
            .map(|b| self.capacity(b).expect("admitted row"))
            .sum();
        let offset = self.payload_start + self.buckets.div_ceil(8) + 8 * (prior + index);
        Some(u64::from_le_bytes(
            self.bytes[offset..offset + 8]
                .try_into()
                .expect("admitted word"),
        ))
    }
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<usize, ParseError> {
    usize::try_from(u32::from_le_bytes(
        bytes[offset..offset + 4].try_into().expect("fixed header"),
    ))
    .map_err(|_| ParseError::InvalidEncoding)
}
