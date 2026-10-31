//! Typed arenas: no unsafe allocation/alignment, growth during decode, or implicit scratch.
#![forbid(unsafe_code)]

use {
    super::{api::StoredOutcome, plan::DecodePlan, shape::SketchShape},
    crate::{
        decode::scratch::{FactorFrame, RowWorkspace, SplitterBasis},
        field::BinaryField,
        types::{DecodeError, RawProduct, UpdateError},
    },
    std::{
        marker::PhantomData,
        mem::size_of,
        sync::{Arc, OnceLock},
    },
};

/// Reusable stable partition storage for one insertion call.
#[derive(Clone, Debug)]
pub struct InsertScratch {
    pub(super) ids: Vec<u64>,
    pub(super) offsets: Vec<usize>,
    pub(super) cursors: Vec<usize>,
}

impl InsertScratch {
    /// Reserve room for at most `max_ids` inputs and `max_buckets` rows per call.
    ///
    /// # Errors
    /// An offset overflows or one of the buffers cannot be reserved.
    pub fn new(max_ids: usize, max_buckets: usize) -> Result<Self, UpdateError> {
        let offsets = max_buckets
            .checked_add(1)
            .ok_or(UpdateError::ScratchTooSmall)?;
        Ok(Self {
            ids: buffer(max_ids).map_err(|_| UpdateError::ScratchTooSmall)?,
            offsets: buffer(offsets).map_err(|_| UpdateError::ScratchTooSmall)?,
            cursors: buffer(max_buckets).map_err(|_| UpdateError::ScratchTooSmall)?,
        })
    }

    pub(super) fn covers(&self, inputs: usize, buckets: usize) -> bool {
        self.ids.len() >= inputs && self.offsets.len() > buckets && self.cursors.len() >= buckets
    }
}

const _: () = {
    assert!(size_of::<RawProduct>() == 16);
    assert!(size_of::<FactorFrame>() == 24);
    assert!(size_of::<StoredOutcome>() == 24);
};

/// Required lengths of typed buffers, excluding unused reusable capacity and fixed handles.
/// Rows run sequentially and reuse the largest row workspace; outputs survive all rows.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ScratchLayout {
    pub(crate) words: usize,
    pub(crate) raw_products: usize,
    pub(crate) factor_frames: usize,
    pub(crate) result_ids: usize,
    pub(crate) outcomes: usize,
    row_start: usize,
    bytes: usize,
}

impl ScratchLayout {
    /// Compute layout from validated row budgets. This sizes storage, never admits work.
    /// Request execution must check candidate/work admission before using this result.
    ///
    /// # Errors
    /// Invalid dimensions/budgets or checked segment/byte arithmetic overflow.
    pub fn for_plan(
        plan: &DecodePlan,
        capacities: &[u16],
        row_budgets: &[Option<usize>],
        beta: usize,
        candidate_count: usize,
    ) -> Result<Self, DecodeError> {
        plan.validate(capacities, row_budgets, beta)?;
        Self::from_rows(
            capacities
                .iter()
                .zip(row_budgets)
                .map(|(&c, &r)| (usize::from(c), r)),
            beta,
            candidate_count,
        )
    }

    #[inline]
    pub(super) fn from_rows(
        rows: impl ExactSizeIterator<Item = (usize, Option<usize>)>,
        beta: usize,
        candidates: usize,
    ) -> Result<Self, DecodeError> {
        let outcomes = rows.len();
        let mut row_words = 0;
        let mut raw_products = 0;
        let mut factor_frames = 0;
        let mut result_ids = 0;
        let mut previous = None;
        for (c, r) in rows {
            if let Some(r) = r {
                let (words, raw) = match previous {
                    Some((capacity, budget, words, raw)) if capacity == c && budget == r => {
                        (words, raw)
                    }
                    _ => {
                        let row = RowLayout::new(c, r)?;
                        previous = Some((c, r, row.words, row.raw_products));
                        (row.words, row.raw_products)
                    }
                };
                row_words = row_words.max(words);
                raw_products = raw_products.max(raw);
                factor_frames = factor_frames.max(r);
                result_ids = checked_add(result_ids, beta)?;
            }
        }
        // Two candidate arrays support a deterministic merge sort. Offsets route rows.
        let row_start = checked_add(checked_mul(2, candidates)?, checked_add(outcomes, 1)?)?;
        let words = checked_add(row_start, row_words)?;
        let bytes = [
            checked_mul(words, 8)?,
            checked_mul(raw_products, 16)?,
            checked_mul(factor_frames, 24)?,
            checked_mul(result_ids, 8)?,
            checked_mul(outcomes, 24)?,
        ]
        .into_iter()
        .try_fold(0, checked_add)?;
        Ok(Self {
            words,
            raw_products,
            factor_frames,
            result_ids,
            outcomes,
            row_start,
            bytes,
        })
    }

    /// Required arena bytes, including outcome metadata and persistent result IDs.
    #[must_use]
    pub fn total_bytes(&self) -> usize {
        self.bytes
    }
}

#[derive(Debug)]
struct NoHintLayout<F: BinaryField> {
    shape: Arc<SketchShape<F>>,
    rows: usize,
    plan: DecodePlan,
    layout: Option<ScratchLayout>,
}

/// Safe owned storage. A job must borrow the entire arena exclusively until its report drops.
#[derive(Debug)]
pub struct DecodeScratch<F: BinaryField> {
    pub(crate) words: Vec<u64>,
    pub(crate) raw: Vec<RawProduct>,
    pub(crate) factors: Vec<FactorFrame>,
    pub(crate) ids: Vec<u64>,
    pub(crate) outcomes: Vec<StoredOutcome>,
    basis: SplitterBasis,
    no_hint_layout: OnceLock<NoHintLayout<F>>,
    field: PhantomData<F>,
}

impl<F: BinaryField> DecodeScratch<F> {
    /// Preallocate all initialized segments outside steady-state decoding.
    ///
    /// # Errors
    /// An allocation cannot be reserved; no partial arena is returned.
    pub fn new(layout: &ScratchLayout) -> Result<Self, DecodeError> {
        Ok(Self {
            words: buffer(layout.words)?,
            raw: buffer(layout.raw_products)?,
            factors: buffer(layout.factor_frames)?,
            ids: buffer(layout.result_ids)?,
            outcomes: buffer(layout.outcomes)?,
            basis: SplitterBasis::default(),
            no_hint_layout: OnceLock::new(),
            field: PhantomData,
        })
    }

    // Memoize one exact shape, row count and plan without adding metadata to algebra.
    // A different key uses normal admission; arena reuse stays bounded.
    pub(super) fn no_hint_layout(
        &self,
        shape: &Arc<SketchShape<F>>,
        rows: usize,
        plan: DecodePlan,
    ) -> Option<&ScratchLayout> {
        let cached = self.no_hint_layout.get_or_init(|| NoHintLayout {
            shape: Arc::clone(shape),
            rows,
            plan,
            layout: no_hint_layout(shape, rows, plan),
        });
        if cached.rows == rows && cached.plan == plan && cached.shape == *shape {
            cached.layout.as_ref()
        } else {
            None
        }
    }

    pub(super) fn covers(&self, layout: &ScratchLayout) -> bool {
        self.words.len() >= layout.words
            && self.raw.len() >= layout.raw_products
            && self.factors.len() >= layout.factor_frames
            && self.ids.len() >= layout.result_ids
            && self.outcomes.len() >= layout.outcomes
    }

    /// Both borrows retain the job's exclusive arena lifetime; publication needs
    /// only results, so completed row roots can be copied without aliasing workspace.
    pub(crate) fn split(
        &mut self,
        layout: &ScratchLayout,
    ) -> (DecodeWorkspace<'_>, ResultStorage<'_>) {
        assert!(self.covers(layout), "split requires admitted scratch");
        let (preprocessing, row) = self.words[..layout.words].split_at_mut(layout.row_start);
        (
            DecodeWorkspace {
                preprocessing,
                row,
                raw: &mut self.raw[..layout.raw_products],
                stack: &mut self.factors[..layout.factor_frames],
                basis: &mut self.basis,
            },
            ResultStorage {
                ids: &mut self.ids[..layout.result_ids],
                outcomes: &mut self.outcomes[..layout.outcomes],
            },
        )
    }
}

pub(crate) struct DecodeWorkspace<'s> {
    pub(crate) preprocessing: &'s mut [u64],
    row: &'s mut [u64],
    raw: &'s mut [RawProduct],
    stack: &'s mut [FactorFrame],
    basis: &'s mut SplitterBasis,
}

pub(crate) struct ResultStorage<'s> {
    pub(crate) ids: &'s mut [u64],
    pub(crate) outcomes: &'s mut [StoredOutcome],
}

impl DecodeWorkspace<'_> {
    /// Tiny probes only borrow the original difference, verification and root slices.
    /// General decoder buffers stay untouched until a probe miss needs them.
    #[inline]
    pub(crate) fn probe_row(&mut self, layout: &RowLayout) -> (&[u64], &mut [u64], &mut [u64]) {
        let words = &mut self.row[..layout.words];
        let verification_start = layout.words - layout.roots - layout.verification;
        let (prefix, outputs) = words.split_at_mut(verification_start);
        let (verification, roots) = outputs.split_at_mut(layout.verification);
        (&prefix[..layout.difference], verification, roots)
    }

    /// Reborrow the maximum-row allocation for one row; roots must be published
    /// before this borrow ends and the next row overwrites the same allocation.
    #[inline]
    pub(crate) fn row(&mut self, layout: &RowLayout) -> (&mut [u64], &mut [u64], RowWorkspace<'_>) {
        let words = &mut self.row[..layout.words];
        let (difference, words) = words.split_at_mut(layout.difference);
        let (syndromes, words) = words.split_at_mut(layout.syndromes);
        let (bm, words) = words.split_at_mut(layout.bm);
        let (polynomials, words) = words.split_at_mut(layout.polynomials);
        let (factors, words) = words.split_at_mut(layout.factors);
        let (square_table, words) = words.split_at_mut(layout.square_table);
        let (verification, roots) = words.split_at_mut(layout.verification);
        (
            self.preprocessing,
            difference,
            RowWorkspace {
                syndromes,
                bm,
                polynomials,
                factors,
                square_table,
                verification,
                roots,
                raw: &mut self.raw[..layout.raw_products],
                stack: &mut self.stack[..layout.roots],
                basis: self.basis,
            },
        )
    }
}

/// Segment lengths inside the reusable row section, in physical storage order.
#[derive(Clone, Debug)]
pub(crate) struct RowLayout {
    pub(crate) difference: usize,
    pub(crate) syndromes: usize,
    pub(crate) bm: usize,
    pub(crate) polynomials: usize,
    pub(crate) factors: usize,
    pub(crate) square_table: usize,
    pub(crate) verification: usize,
    pub(crate) roots: usize,
    pub(crate) words: usize,
    pub(crate) raw_products: usize,
}

impl RowLayout {
    #[inline]
    pub(crate) fn new(c: usize, r: usize) -> Result<Self, DecodeError> {
        let mut end = 0;
        let mut segment = |len| {
            end = checked_add(end, len)?;
            Ok::<_, DecodeError>(len)
        };
        let difference = segment(c)?;
        let syndromes = segment(checked_add(checked_mul(2, c)?, 1)?)?;
        let bm = segment(checked_mul(4, checked_add(c, 1)?)?)?;
        let width = checked_add(r, 1)?;
        let polynomials = segment(if r == 0 { 0 } else { checked_mul(8, width)? })?;
        let factors = segment(if r == 0 {
            0
        } else {
            checked_mul(2, checked_mul(width, width)?)?
        })?;
        let square_table = segment(checked_mul(r, r / 2)?)?;
        let verification = segment(c)?;
        let roots = segment(r)?;
        let raw_products = if r == 0 {
            0
        } else {
            checked_mul(2, checked_add(r, 2)?)?
        };
        Ok(Self {
            difference,
            syndromes,
            bm,
            polynomials,
            factors,
            square_table,
            verification,
            roots,
            words: end,
            raw_products,
        })
    }
}

fn buffer<T: Default + Clone>(len: usize) -> Result<Vec<T>, DecodeError> {
    let mut values = Vec::new();
    values
        .try_reserve_exact(len)
        .map_err(|_| DecodeError::ScratchTooSmall)?;
    values.resize(len, T::default());
    Ok(values)
}
fn checked_add(a: usize, b: usize) -> Result<usize, DecodeError> {
    a.checked_add(b).ok_or(DecodeError::ScratchTooSmall)
}
fn checked_mul(a: usize, b: usize) -> Result<usize, DecodeError> {
    a.checked_mul(b).ok_or(DecodeError::ScratchTooSmall)
}

// Only immutable dimensions are cached. Admission still checks peer shape, plan,
// candidates, zero membership, limits and actual scratch coverage on every call.
fn no_hint_layout<F: BinaryField>(
    shape: &SketchShape<F>,
    count: usize,
    plan: DecodePlan,
) -> Option<ScratchLayout> {
    let beta = usize::from(shape.capacities()[0]);
    if shape.capacities().iter().any(|&c| usize::from(c) != beta) {
        return None;
    }
    let rows = || std::iter::repeat_n((beta, Some(beta)), count);
    plan.work_bound(rows(), beta, 0).ok()?;
    ScratchLayout::from_rows(rows(), beta, 0).ok()
}

#[cfg(test)]
mod v3_cache_tests;
