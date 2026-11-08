# Original root traversal stages and AVX square heap effects

All 344 native executable obligations remain in scope. This checkpoint
adds exact original Aeneas body refinements for `Roots::run`,
`Roots::divide`, the affine subspace offset, and `affine::splitter`.
Production Rust and Cargo inputs are unchanged.

The stock root-run projection retains the original dispatcher and
subspace offset helper. Its theorem checks the stage decisions, exact
workspace frames, and all admitted branches. The original leaf,
closed-leaf, trace, reducer table, GCD, factor division and splitter
bodies are bound in the projection. Affine preparation and enumeration
retain explicit typed slots. The GCD stage uses the
admitted div/rem law and normalized remainder and retry conditions.
Table, GCD and affine split prices follow the original order of
checked operations, including intermediate overflow.

The splitter theorem checks the original setup, the complete coefficient
loop, prefix normalization and all slice writebacks. It binds the
original linear evaluation and Dense modular square bodies under the
field, reducer table and backend contracts. Relating the splitter result
to the affine coset maintained by the complete traversal remains open.

The original divide theorem checks both charge results, a nonexact
division, both checked offset overflows, and the affine and non-affine
commits. It returns the exact quotient and remainder scratch, pending
right-child coefficients, stack record, left modulus, meter, and stage.
The original Dense exact-division wrapper is bound under the explicit
div/rem model law. The original div/rem body linkage and the
depth-first and affine traversal invariants remain open.

The AVX square finite-heap theorem composes the zero fill, scalar
coefficient seeds, and the original masked LLBC load/store block
trace. Under the admitted allocation views, it preserves the input
and table and changes exactly the modeled words of the two mutable
slices. The captured x86 RawProduct layout uses stride 16, alignment
8 and word offsets 0 and 8. The verifier checks that specific layout
and rejects target and overlap mutations. The layout premise is
capture-specific. Actual Rust pointer provenance, compiled scalar
stores and full compiler-to-ISA correspondence remain open.

Run the complete gate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
