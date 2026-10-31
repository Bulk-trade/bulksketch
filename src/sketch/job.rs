//! One exclusive arena loan; verified rows remain private until successful finish.
#![forbid(unsafe_code)]

use {
    super::{
        api::{DecodeOutcome, DecodeReport, DecodeRequest, Publication, admit_request},
        candidates,
        contract::{RequestDecoder, RequestExecution},
        dispatch::{DecodeExecution, Decoder, run_probe},
        input::{DecodeRowsRequest, RequestInput},
        scratch::{DecodeScratch, DecodeWorkspace, RowLayout},
    },
    crate::{
        decode::{
            row::{RowBudget, RowInput, RowResult},
            work::{Charge, WorkScheduleV1},
        },
        field::BinaryField,
        types::{DecodeError, DecodeFailure, Stage, StageProgress, WorkMeter},
    },
};

#[expect(
    clippy::large_enum_variant,
    reason = "inline row state avoids an allocation for every decoded row"
)]
enum JobState<F: BinaryField> {
    Row {
        execution: DecodeExecution<F>,
        layout: RowLayout,
        zero: bool,
    },
    Complete,
    Error(DecodeError),
}

/// Staged, deterministic decode. Dropping a job publishes nothing and releases its arena.
pub type DecodeJob<'r, 's, F> = Job<'r, 's, F, DecodeRequest<'r, F>>;

/// Shared staged driver with a statically selected request representation.
pub struct Job<'r, 's, F: BinaryField, R> {
    request: R,
    decoder: &'r Decoder<F>,
    workspace: DecodeWorkspace<'s>,
    publication: Publication<'s>,
    meter: WorkMeter,
    peak: usize,
    bucket: usize,
    word_offset: usize,
    candidate_count: usize,
    state: JobState<F>,
}

impl<F: BinaryField, R: RequestInput<F>> std::fmt::Debug for Job<'_, '_, F, R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DecodeJob")
            .field("bucket", &self.bucket)
            .field("stage", &self.next_stage())
            .field("work", &self.meter.used())
            .finish_non_exhaustive()
    }
}

impl<'r, 's, F: BinaryField> DecodeJob<'r, 's, F> {
    /// Admit the complete request before preprocessing or algebra. Tight work limits may
    /// still fail during subsequent stages; no constructor error publishes a report.
    ///
    /// # Errors
    /// Shape, plan, raw candidate count, work, then scratch failures, in contract order.
    #[inline]
    pub fn new(
        request: DecodeRequest<'r, F>,
        decoder: &'r Decoder<F>,
        scratch: &'s mut DecodeScratch<F>,
    ) -> Result<Self, DecodeError> {
        Self::from_request(request, decoder, scratch)
    }
}

impl<'r, 's, F: BinaryField, R: RequestInput<F>> Job<'r, 's, F, R> {
    #[inline]
    fn from_request(
        request: R,
        decoder: &'r Decoder<F>,
        scratch: &'s mut DecodeScratch<F>,
    ) -> Result<Self, DecodeError> {
        let admitted = admit_request(&request, scratch)?;
        debug_assert!(admitted.zero_failures <= request.bucket_count());
        let (workspace, results) = scratch.split(&admitted.layout);
        let publication = Publication::new(results, &admitted.layout);
        let mut job = Self {
            candidate_count: request.candidate_count()?,
            request,
            decoder,
            workspace,
            publication,
            meter: admitted.meter,
            peak: admitted.layout.total_bytes(),
            bucket: 0,
            word_offset: 0,
            state: JobState::Complete,
        };
        job.meter.charge(WorkScheduleV1::cost(Charge::Normalize {
            inputs: job.candidate_count,
        })?)?;
        job.request.normalize(job.workspace.preprocessing);
        job.prepare_row()?;
        Ok(job)
    }

    /// The next row stage, or `None` after completion or terminal request failure.
    #[must_use]
    pub fn next_stage(&self) -> Option<Stage> {
        match &self.state {
            JobState::Row { execution, .. } => execution.next_stage(),
            JobState::Complete | JobState::Error(_) => None,
        }
    }

    /// Run one stage. Counters reveal no provisional IDs or row classifications.
    /// A terminal request failure is sticky, including on repeated calls.
    ///
    /// # Panics
    /// Called after successful completion (`next_stage() == None`).
    #[inline(always)]
    pub fn run_next(&mut self) -> StageProgress {
        match self.advance() {
            Ok(progress) => progress,
            Err(error) => {
                self.state = JobState::Error(error);
                self.publication.fail(error);
                StageProgress::Failed(error)
            }
        }
    }

    /// Drain and consume this job. Only a successful complete request lends results.
    ///
    /// # Errors
    /// A request-wide failure discards every earlier row result.
    #[inline]
    pub fn finish(self) -> Result<DecodeReport<'s>, DecodeError> {
        <Self as RequestExecution<'s>>::finish(self)
    }

    #[inline(always)]
    fn prepare_row(&mut self) -> Result<(), DecodeError> {
        let beta = self.request.limits().max_output_per_bucket;
        for (capacity, row) in self.request.remaining_rows(self.bucket, self.word_offset) {
            let zero = row.zero;
            let Some(nonzero) = beta.checked_sub(usize::from(zero)) else {
                self.publication.write(
                    self.bucket,
                    DecodeOutcome::Failed {
                        reason: DecodeFailure::DegreeExceedsBudget,
                    },
                    false,
                );
                self.word_offset += capacity;
                self.bucket += 1;
                continue;
            };
            self.meter
                .charge(WorkScheduleV1::cost(Charge::Compare { capacity })?)?;
            // Compare owns inspection of this row, including warm cached bytes.
            // Never populate an immutable encoding merely to seek equality.
            let cached = row.local.encoded_v1.get();
            #[cfg(test)]
            let cached = cached.filter(|_| !self.decoder.skip_shortcuts);
            let cached_equal = !zero
                && cached.is_some_and(|bytes| {
                    let syndrome_start = bytes.len() - 8 * row.local.shape.total_syndrome_words();
                    let range = 8 * row.word_offset..8 * (row.word_offset + capacity);
                    #[cfg(test)]
                    crate::backend::test_observer::cached_comparison(self.bucket, 1);
                    bytes[syndrome_start + range.start..syndrome_start + range.end] == *row.remote
                });
            if cached_equal {
                self.publication
                    .write(self.bucket, DecodeOutcome::Equal, false);
                self.word_offset += capacity;
                self.bucket += 1;
                continue;
            }
            let layout = RowLayout::new(capacity, nonzero)?;
            let (_, difference, _) = self.workspace.row(&layout);

            // Compare owns construction of this row's immutable difference.
            // Future rows remain untouched until their own Compare succeeds.
            let different = (self.decoder.difference)(
                difference,
                &row.local.words[row.word_offset..row.word_offset + capacity],
                row.remote,
            );
            if zero || different {
                let budget = RowBudget {
                    nonzero,
                    total: beta,
                };
                let probe = if self.request.plan().has_probes() {
                    self.decoder.begin_probe(budget, difference)
                } else {
                    None
                };
                if let Some(execution) = probe {
                    self.state = JobState::Row {
                        execution,
                        layout,
                        zero,
                    };
                } else if let JobState::Row {
                    execution,
                    layout: previous_layout,
                    zero: previous_zero,
                } = &mut self.state
                {
                    self.decoder.restart(execution, budget);
                    *previous_layout = layout;
                    *previous_zero = zero;
                } else {
                    self.state = JobState::Row {
                        execution: self.decoder.begin(budget),
                        layout,
                        zero,
                    };
                }
                if self.request.plan().is_v3() {
                    let JobState::Row { execution, .. } = &mut self.state else {
                        unreachable!("prepared row");
                    };
                    execution.enable_v3();
                    if different {
                        execution.start_degrees(capacity);
                    }
                }
                return Ok(());
            }
            self.publication
                .write(self.bucket, DecodeOutcome::Equal, false);
            self.word_offset += capacity;
            self.bucket += 1;
        }
        self.state = JobState::Complete;
        Ok(())
    }

    #[inline(always)]
    fn advance(&mut self) -> Result<StageProgress, DecodeError> {
        let (execution, layout, zero) = match &mut self.state {
            JobState::Row {
                execution,
                layout,
                zero,
            } => (execution, layout, zero),
            JobState::Error(error) => return Err(*error),
            JobState::Complete => panic!("completed decode job"),
        };
        let bucket = self.bucket;
        let (progress, complete) = if let DecodeExecution::Probe(probe, backend) = execution {
            let (difference, verification, roots) = self.workspace.probe_row(layout);
            let progress = run_probe::<F>(
                *backend,
                probe,
                difference,
                verification,
                roots,
                &mut self.meter,
            )?;
            if probe.next_stage() == Some(Stage::Canonicalization)
                && roots[..probe.count()]
                    .iter()
                    .any(|&id| !self.request.permits_id(bucket, id))
            {
                probe.reject(difference.len());
            }
            let complete = probe.next_stage().is_none();
            if complete {
                self.publication.write(
                    bucket,
                    DecodeOutcome::Decoded {
                        ids: &roots[..probe.count()],
                    },
                    *zero,
                );
            } else if probe.next_stage() == Some(Stage::Reconstruction) {
                *execution = self.decoder.begin(RowBudget {
                    nonzero: self.request.limits().max_output_per_bucket - usize::from(*zero),
                    total: self.request.limits().max_output_per_bucket,
                });
                if self.request.plan().is_v3() {
                    execution.enable_v3();
                    execution.start_degrees(difference.len());
                }
            }
            (progress, complete)
        } else {
            let (preprocessing, difference, mut workspace) = self.workspace.row(layout);
            let input = RowInput {
                difference,
                candidates: candidates::row(preprocessing, self.candidate_count, bucket),
            };
            let progress = execution.run_next(input, &mut workspace, &mut self.meter)?;
            if self.request.plan().is_v3()
                && progress.stage == Stage::Verification
                && execution.next_stage() == Some(Stage::Canonicalization)
                && workspace.roots[..execution.verification_count()]
                    .iter()
                    .any(|&id| id == 0 || !self.request.permits_id(bucket, id))
            {
                execution.reject_upper(difference.len());
            }
            let complete = execution.next_stage().is_none();
            if complete {
                let outcome = match execution.completed_result(&workspace)? {
                    RowResult::Equal => DecodeOutcome::Equal,
                    RowResult::Failed(reason) => DecodeOutcome::Failed { reason },
                    RowResult::Decoded(ids) => {
                        if ids
                            .iter()
                            .all(|&id| id != 0 && self.request.permits_id(bucket, id))
                        {
                            DecodeOutcome::Decoded { ids }
                        } else {
                            DecodeOutcome::Failed {
                                reason: DecodeFailure::InvalidLocator,
                            }
                        }
                    }
                };
                self.publication.write(bucket, outcome, *zero);
            }
            (progress, complete)
        };
        if complete {
            self.word_offset += layout.difference;
            self.bucket += 1;
            // The following Compare remains part of the terminal observation.
            self.prepare_row()?;
        }
        Ok(StageProgress::Completed {
            bucket,
            stage: progress.stage,
            work: self.meter.used(),
            peak_scratch_bytes: self.peak,
            locator_degree: progress.locator_degree,
            candidate_hits: progress.candidate_hits,
            trace_attempts: progress.trace_attempts,
            gcd_degree: progress.gcd_degree,
        })
    }
}

impl<F: BinaryField> RequestDecoder<F> for Decoder<F> {
    type Job<'r, 's> = DecodeJob<'r, 's, F>;
    #[inline]
    fn new_job<'r, 's>(
        &'r self,
        request: DecodeRequest<'r, F>,
        scratch: &'s mut DecodeScratch<F>,
    ) -> Result<Self::Job<'r, 's>, DecodeError> {
        DecodeJob::new(request, self, scratch)
    }
}

impl<'s, F: BinaryField, R: RequestInput<F>> RequestExecution<'s> for Job<'_, 's, F, R> {
    fn next_stage(&self) -> Option<Stage> {
        self.next_stage()
    }
    fn run_next(&mut self) -> StageProgress {
        self.run_next()
    }
    #[inline]
    fn finish(mut self) -> Result<DecodeReport<'s>, DecodeError> {
        while <Self as RequestExecution<'s>>::next_stage(&self).is_some() {
            <Self as RequestExecution<'s>>::run_next(&mut self);
        }
        self.publication.finish(self.meter.used(), self.peak)
    }
}

/// Admit and finish the same staged job used by instrumented callers.
///
/// # Errors
/// Constructor errors propagate unchanged; execution errors publish no report.
pub fn decode_into<'s, F: BinaryField>(
    request: DecodeRequest<'_, F>,
    decoder: &Decoder<F>,
    scratch: &'s mut DecodeScratch<F>,
) -> Result<DecodeReport<'s>, DecodeError> {
    decoder.new_job(request, scratch)?.finish()
}

/// Decode independent borrowed GF64 row payloads with one ordinary staged job.
///
/// # Errors
/// Rejects empty batches, multirow locals and wrong payload lengths as
/// `ShapeMismatch`, then applies the ordinary plan, candidate, work and scratch
/// precedence. No request failure exposes partial results.
pub fn decode_rows_into<'s, F: BinaryField>(
    request: DecodeRowsRequest<'_, F>,
    decoder: &Decoder<F>,
    scratch: &'s mut DecodeScratch<F>,
) -> Result<DecodeReport<'s>, DecodeError> {
    Job::from_request(request, decoder, scratch)?.finish()
}

#[cfg(test)]
mod v2_tests;

#[cfg(test)]
mod prepared_tests;

#[cfg(test)]
mod v3_rejection_tests;

#[cfg(test)]
mod small_degree_tests;
