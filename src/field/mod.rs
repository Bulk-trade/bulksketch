//! Canonical field identity, arithmetic and test-only tiny fields.
#![forbid(unsafe_code)]

use crate::types::FieldId;

#[cfg(test)]
pub(crate) mod arithmetic_tests;
#[cfg(test)]
mod constant_tests;
#[cfg(any(target_arch = "x86_64", test))]
pub(crate) mod frobenius;
pub(crate) mod gf64;
pub(crate) mod maps;
mod quadratic_chunks;
#[cfg(test)]
pub(crate) mod reference;
#[cfg(test)]
pub(crate) mod tiny;

pub(crate) mod sealed {
    pub trait Sealed {}
}

/// Closed field specification. Kernels consume canonical words, never masked IDs.
pub trait BinaryField: sealed::Sealed + Copy + Eq + Send + Sync + 'static {
    /// Extension degree over GF(2).
    const BITS: u32;
    /// Irreducible polynomial without its leading term.
    const MODULUS_LOW: u64;
    /// Registered polynomial/basis identity.
    const WIRE_ID: FieldId;
    /// Canonical element mask.
    const MASK: u64;
}

/// Full-width GF(2^64) identity field.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Gf64;
impl sealed::Sealed for Gf64 {}
impl BinaryField for Gf64 {
    const BITS: u32 = 64;
    const MODULUS_LOW: u64 = 0x1b;
    const WIRE_ID: FieldId = FieldId::Gf64;
    const MASK: u64 = u64::MAX;
}
