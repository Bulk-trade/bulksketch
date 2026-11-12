# Frobenius tables and slice kernels

The later [slice and normalization checkpoint](SLICE_NORMALIZATION.md) resolves
the mutable Zip and Dense iterator dependencies listed below.

The two original Frobenius generators complete normally and produce all 2,560
cells. Each cell is the scheduled power of the square map applied to a nibble
placed at its four-bit offset. The shared table contains nine maps for powers
1 through 7, 15 and 31. The separate inverse table contains the 21st power.

The main generator proof follows all six original loops. It tracks each basis
column through the scheduled squarings, then uses the least set bit recurrence
to construct every nibble entry. The inverse generator proof tracks the
contribution of each basis bit across the row. Both proofs check the shifts,
counters, casts, indexing and nested updates. The two static initializer
statements follow from those same source-body proofs.

The lookup proofs follow the original selector and 16-row scan. XOR linearity
connects the accumulated nibble images to the full word image. Every U32 selector
outside the supported schedule returns `None`, and `inverse21` returns the full
21st Frobenius image for every U64 input. The original x86-visible Rust bodies
were extracted for `x86_64-apple-darwin` with the pinned tools. The proof consumes
the generated initializer bodies. Correspondence to Rust's constant evaluation
and target execution stays within the documented extraction trust boundary.

The slice checkpoint proves the original `BulkKernels::multiply_linear` default
for every slice length. The descending update reads the original preceding
coefficient and preserves the full fixed-length destination frame. Its contract
requires the supplied multiplication to agree with the native GF64 body.
With a zero final spare slot, the resulting Mathlib polynomial is the full
product with `1 + root * X`. The default `square_mod` fallback returns false and
preserves both mutable buffers in the slice value model.

The six new source bodies bring the ledger to 32 refinements across 344 retained
native obligations. The static statements and polynomial transport add no
extra source-body count. The slice frame proofs use the pinned Aeneas value
model. Decoder completeness, machine memory and aliasing, and the accelerated
ISA contracts remain open.

The existing x86_64 Frobenius regeneration regression passed under Rosetta
with the pinned nightly toolchain. The arm64 release suite passed all 139 tests
with Rust 1.96.1.

The next slice work includes the mutable `Zip` backward updates used by
Portable XOR. The dense coefficient update also needs the standard iterator
`rposition` and `Option.map_or` models. The extraction receipts record the
successful source boundaries and these outstanding tool gaps.
