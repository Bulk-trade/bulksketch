//! Canonical-row decoding; no sketch/shape/wire or public arena dependencies.
#![forbid(unsafe_code)]

pub(crate) mod row;
pub(crate) mod scratch;
pub(crate) mod work;

mod bm;
#[cfg(test)]
mod bm_tests;
pub(crate) mod direct;

mod affine;
mod deg34;
mod degree_probe;
pub(crate) mod probe;
mod roots;
pub(crate) mod stages;
mod verify;

#[cfg(test)]
mod row_tests;
