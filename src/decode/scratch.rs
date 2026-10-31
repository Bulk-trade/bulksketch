//! Lower workspace borrows, owned by the upper request arena. The row decoder consumes these.
#![forbid(unsafe_code)]

use crate::types::RawProduct;

#[derive(Default)]
pub(crate) struct SplitterBasis {
    pub(crate) directions: Option<[u64; 64]>,
    pub(crate) len: u32,
}

impl std::fmt::Debug for SplitterBasis {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SplitterBasis").finish_non_exhaustive()
    }
}

/// An explicit factor-stack entry. The parent table is released before children start.
#[derive(Clone, Debug, Default)]
#[repr(C)]
pub(crate) struct FactorFrame {
    pub(crate) coefficient_start: u64,
    pub(crate) coefficient_len: u64,
    pub(crate) next_direction: u32,
    pub(crate) split_checked: u32,
}

/// Consecutive words, never a public arena or a replaceable scratch handle.
pub(crate) struct RowWorkspace<'w> {
    pub(crate) syndromes: &'w mut [u64],
    pub(crate) bm: &'w mut [u64],
    pub(crate) polynomials: &'w mut [u64],
    pub(crate) factors: &'w mut [u64],
    pub(crate) square_table: &'w mut [u64],
    pub(crate) verification: &'w mut [u64],
    pub(crate) roots: &'w mut [u64],
    pub(crate) raw: &'w mut [RawProduct],
    pub(crate) stack: &'w mut [FactorFrame],
    pub(crate) basis: &'w mut SplitterBasis,
}
