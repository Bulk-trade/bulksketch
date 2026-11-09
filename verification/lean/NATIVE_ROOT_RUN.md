# Original root traversal stages and AVX square heap effects

All 344 native executable obligations remain in scope. This checkpoint
adds exact original Aeneas body refinements for `Roots::run`,
`Roots::divide`, the affine subspace offset, `affine::splitter`,
`affine::subspaces`, and the preparation and enumeration wrappers.
Production Rust and Cargo inputs are unchanged.

The stock root-run projection retains the original dispatcher and
subspace offset helper. Its theorem checks the stage decisions, exact
workspace frames, and all admitted branches. The original leaf,
closed-leaf, trace, reducer table, GCD, factor division, splitter,
affine preparation and affine enumeration wrappers are bound in the
projection. The affine multiple, binary solve map, enumeration selector
and candidate enumeration still have typed slots. The GCD stage uses the
admitted div/rem law and normalized remainder and retry conditions.
Table, GCD and affine split prices follow the original order of
checked operations, including intermediate overflow.

The splitter theorem checks the original setup, the complete coefficient
loop, prefix normalization and all slice writebacks. It binds the
original linear evaluation and Dense modular square bodies under the
field, reducer table and backend contracts. The field proof relates the
normalized output to both child cosets at every root of the factor in
the parent coset. It requires independence of the new basis direction.
The complete traversal still needs to establish and preserve those premises.

The affine subspace table proof checks the seed, both loops and exact
row writes. Over Mathlib's GF(2⁶⁴), each prefix row represents the
polynomial whose zero set is the binary span of those directions. The
proof starts with `A₀ = X` and establishes `Aᵣ₊₁ = Aᵣ² + Aᵣ(bᵣ)Aᵣ`.

Affine preparation checks the exact charge, the zero linear coefficient,
the solve-map rejection, both rank guards, and both successful stages.
The split path invokes the original subspace table implementation. Affine
enumeration checks the exact price, both candidate-result frames, the
bounded count increment and the original advance after success. The
inner enumeration algorithm and Gaussian elimination remain open.

The original divide theorem checks both charge results, a nonexact
division, both checked offset overflows, and the affine and non-affine
commits. It returns the exact quotient and remainder scratch, pending
right-child coefficients, stack record, left modulus, meter, and stage.
The original Dense exact-division wrapper is bound to the proved div/rem
body in the specialization. Depth-first and affine traversal invariants
remain open.

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
