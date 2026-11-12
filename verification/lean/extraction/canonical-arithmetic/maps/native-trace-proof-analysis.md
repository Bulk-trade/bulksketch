# Original native trace proof analysis

Analysis date: 2026-11-04. Exact hashes are recorded in
`bridge/audit/frozen-inputs.json`. This note describes the source argument; it does
not include a build or replay run.

The `trace_refines` type is exactly the fixed unconditional challenge. For every
source U64 input, the real Gf64 dictionary produces `Result.ok` of the complete
specified U8 selector. No successful-return or canonical-input restriction is
assumed.

The full Gf64 MASK establishes canonicality for every word. The actual BITS-64
branch is selected from the real dictionary. The generic fallback remains in
the unchanged generated function. Both native shifts, by 61 and 63, are below
64 and have exact normal runtime equations for every input.

`selector_bounded` uses `Nat.and_le_right` to bound the XOR/AND result by one.
`selector_conversion_normal` discharges the checked u64-to-u8 conversion
condition and proves an inner Rust `Ok` with the complete specified byte. The
source `expect` consequently takes its success branch, independently of any
Debug formatter or diagnostic assumption. The concrete runtime models retain
full range-checked conversion. Error and formatting correspondence remain
explicit runtime and compiler assumptions; conversion success is proved rather
than supplied by a stub.

The selector retains every byte bit: the low bit is input coefficient 61 XOR
coefficient 63, and all remaining bits are zero. The proof unfolds the original
generated endpoint and `expect` only after establishing the inner `Ok` result.
No original source branch is deleted.

This theorem establishes native selector behavior. Identification with the
absolute trace of all 64 conjugates is specified by the separate
`MapsTraceMathChallenge`. Targeted elaboration, transitive-axiom checks and
aggregate kernel/Nanoda replay are separate verification results, rather than
executions performed for this source analysis.
