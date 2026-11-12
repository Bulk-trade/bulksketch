# Native Newton guard and residual recurrence

The ledger retains 344 native executable obligations. The associated record
contains 96 original Aeneas body refinements under their stated contracts and five
separate source-linked LLBC contracts. Production Rust is unchanged.

## Exact native result and scratch

The original degree-three/four guard reads the admitted odd syndrome prefix
and computes the exact clearing denominator. A zero denominator returns
false and preserves the input scratch. The scratch length requirement
applies only to the writing branch. A nonzero denominator writes the five
cleared coefficients and denominator before checking residuals. The proof
establishes every written slot and the exact original suffix, including
when a later residual rejects.

Both original instances of all three nested loop levels have checked
refinements. The scan checks the available indices from the degree up to
the smaller of the odd-row length and degree plus two. Each lag computes
the original positive power, trailing-zero count, odd-row index and
repeated square. The exponent and slice bounds cover every read. The
loops return the exact short-circuit boolean and leave the coefficient
scratch untouched.

## Field meaning

The cubic and quartic word formulas transport to their exact characteristic
two Newton systems. Under the stated moment identities, the five cleared
words are the monic coefficient list scaled by the source denominator.
The unused fifth cubic word is zero. For an odd row representing three or
four roots, the denominator equals the corresponding Vandermonde
pair-sum product. Distinct roots make that product nonzero.

The guard's residual boolean is equivalent to vanishing of the selected
cleared recurrence equations over GF64. The repeated-square proof
reconstructs each required power sum from the exact odd power sum and its
power-of-two factor. The support theorem composes the original guard with
the locator recurrence. It proves acceptance for an admitted odd row when
the nonzero denominator and cleared coefficients agree with the support
locator. The coefficient transport and residual semantics are independent
checked endpoints.

## Checked extraction

The original guard, all six loop wrappers and all six loop bodies are
retained verbatim. The isolated checked nested-slice retry extends the
pinned scalar-array fixed-point matcher. It runs only in the
continuation-free fixed-point list join under the same immediate outer
mutable borrow ID. It requires a U64 slice and an equally typed symbolic
shared payload. The stock retry ends the shared side and preserves the
mutable update continuation. The old matcher modes remain in force.

The gate checks the exact original LLBC, translator roles, recorded
commands and replay hashes. It applies the full patch and the base patch
followed by the delta to separate pinned source copies and compares the
results. Pinned and unchecked original runs retain their rejection.
The ten matcher controls and separate quartic and normalization controls
are recorded with the extraction.

Run `python3 scripts/verify_all.py` from `verification/lean` under the pinned
toolchain for the frozen statements, transitive axiom audit, kernel and
Nanoda replays, and rejection controls.

## Scope of the recorded component results

These limits describe the component record below. The
[verification overview](README.md) states the combined Portable result and
links the other source refinements.

The extraction records include the original degree probe with scoped
standard-library bindings and the original Berlekamp–Massey locator with both
typed mutable continuations preserved. Their functional contracts are described
in the [degree-probe/BM loop proofs](NATIVE_BM_DEGREE_PROBE.md) and
[locator proofs](NATIVE_BM_LOCATOR.md). The [overview](README.md) states the
combined Portable result. Accelerated execution, physical memory provenance,
ISA and compiler-expanded correspondence are outside these component proofs.
