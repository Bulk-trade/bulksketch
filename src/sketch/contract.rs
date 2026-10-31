//! Request entry points implemented by the decode job on top of the row driver.
//! No public incomplete decode function is declared.
#![forbid(unsafe_code)]

use {
    super::{
        api::{DecodeReport, DecodeRequest},
        scratch::DecodeScratch,
    },
    crate::{
        field::BinaryField,
        types::{DecodeError, Stage, StageProgress},
    },
};

/// Finish drains; request errors suppress all rows. Drop publishes nothing.
pub(crate) trait RequestExecution<'s> {
    fn next_stage(&self) -> Option<Stage>;
    fn run_next(&mut self) -> StageProgress;
    fn finish(self) -> Result<DecodeReport<'s>, DecodeError>;
}

/// Whole-operation selection stays in sketch, never backend. The ordinary decode
/// entry point must propagate `new_job` errors unchanged, then call consuming finish.
pub(crate) trait RequestDecoder<F: BinaryField> {
    type Job<'r, 's>: RequestExecution<'s>
    where
        Self: 'r;
    fn new_job<'r, 's>(
        &'r self,
        request: DecodeRequest<'r, F>,
        scratch: &'s mut DecodeScratch<F>,
    ) -> Result<Self::Job<'r, 's>, DecodeError>;
}
