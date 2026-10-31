//! Thread-local operation entries, including work performed during job construction.
#![forbid(unsafe_code)]
use std::cell::Cell;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Entries {
    pub(crate) differences: usize,
    pub(crate) inverses: usize,
}
thread_local! {
    static ENTRIES: Cell<Entries> = const { Cell::new(Entries { differences: 0, inverses: 0 }) };
    static CACHED_COMPARISONS: Cell<CachedComparisons> = const {
        Cell::new(CachedComparisons { rows: 0, end: 0 })
    };
}
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct CachedComparisons {
    pub(crate) rows: usize,
    pub(crate) end: usize,
}
pub(crate) fn reset() {
    ENTRIES.set(Entries::default());
    CACHED_COMPARISONS.set(CachedComparisons::default());
}
pub(crate) fn entries() -> Entries {
    ENTRIES.get()
}
pub(crate) fn difference() {
    let mut e = ENTRIES.get();
    e.differences += 1;
    ENTRIES.set(e);
}
pub(crate) fn inverse() {
    let mut e = ENTRIES.get();
    e.inverses += 1;
    ENTRIES.set(e);
}
pub(crate) fn cached_comparison(first: usize, rows: usize) {
    let mut e = CACHED_COMPARISONS.get();
    e.rows += rows;
    e.end = e.end.max(first + rows);
    CACHED_COMPARISONS.set(e);
}
pub(crate) fn cached_comparisons() -> CachedComparisons {
    CACHED_COMPARISONS.get()
}
