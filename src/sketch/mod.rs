//! Request-level shape, wire, admission and ownership.
#![forbid(unsafe_code)]

pub(crate) mod api;
mod candidates;
pub(crate) mod contract;
mod dispatch;
mod input;
mod job;
mod plan;
pub(crate) mod scratch;
mod shape;
mod state;
mod wire;

pub use {
    api::{DecodeLimits, DecodeOutcome, DecodeReport, DecodeRequest},
    dispatch::Decoder,
    input::{DecodeRow, DecodeRowsRequest},
    job::{DecodeJob, decode_into, decode_rows_into},
    plan::DecodePlan,
    scratch::{DecodeScratch, InsertScratch, ScratchLayout},
    shape::{ShapeLimits, SketchShape},
    state::{FrozenSketch, MutableSketch},
    wire::{ParseLimits, SketchView},
};

#[cfg(test)]
mod tests;

#[cfg(test)]
mod state_tests;

#[cfg(test)]
mod wire_tests;

#[cfg(test)]
mod decode_tests;

#[cfg(test)]
mod v1_plan_tests;

#[cfg(test)]
mod forced_dispatch_tests;

#[cfg(test)]
mod backend_work_tests;
#[cfg(test)]
mod forced_backend_tests;
