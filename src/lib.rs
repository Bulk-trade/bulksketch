//! Native binary-syndrome reconciliation with bounded, deterministic GF64 decoding.
#![deny(unsafe_code)]
#![warn(missing_docs)]

mod backend;
mod decode;
mod field;
mod poly;
mod sketch;
mod types;

pub use {
    field::{BinaryField, Gf64},
    sketch::{
        DecodeJob, DecodeLimits, DecodeOutcome, DecodePlan, DecodeReport, DecodeRequest, DecodeRow,
        DecodeRowsRequest, DecodeScratch, Decoder, FrozenSketch, InsertScratch, MutableSketch,
        ParseLimits, ScratchLayout, ShapeLimits, SketchShape, SketchView, decode_into,
        decode_rows_into,
    },
    types::{
        BackendError, BackendId, BackendRequest, CreateError, DecodeError, DecodeFailure,
        EncodeError, FieldId, ParseError, ShapeError, ShapeMismatch, Stage, StageProgress,
        UpdateError, WorkUnits,
    },
};
