# Original root traversal stages and AVX square heap effects

All 344 native executable obligations remain in scope. This checkpoint
adds exact original Aeneas body refinements for `Roots::run`,
`Roots::divide`, the affine subspace offset, `affine::splitter`,
`affine::subspaces`, the preparation and enumeration wrappers, the
inner enumerator and selector, the GF64 solve map and its table
construction, and the original AVX linear update and Horner paths.
Production Rust and Cargo inputs are unchanged.

The stock root-run projection retains the original dispatcher and
subspace offset helper. Its theorem checks the stage decisions, exact
workspace frames, and all admitted branches. The original leaf,
closed-leaf, trace, reducer table, GCD, factor division, splitter,
affine preparation and affine enumeration wrappers are bound in the
projection. The original selector, binary solve map, and candidate
enumerator are bound directly. The affine multiple still has a typed
slot. The GCD stage uses the
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
inner enumerator proof checks the rank shift, scratch split, batch
boundaries, Gray points, Horner calls, exact candidate writes and final
count. The proved frame supplies the wrapper's candidate law under
admitted scratch and rank bounds. The original Portable, PCLMUL, and
AVX-512 Horner methods provide the field-evaluation law when installed
in the backend slot under their contracts. The completeness theorem
returns every factor root exactly once if the factor splits into
distinct nonzero roots in the affine coset and the directions are
independent. It verifies the count, the exact returned root set, and
both scratch widths.

The original GF64 solve-map proof checks native table construction,
the coefficient fold, pivot insertion and reduction, and exact kernel,
image and preimage writes. Its field interpretation proves the
returned base maps to the constant term and each written kernel
direction maps to zero. Showing that those directions span the entire
kernel is still a separate obligation.

The enumeration selector and its square-products helper check all
scalar inputs. Their proofs preserve the checked operation order,
including the rank cast, optional shift and multiplication, and
checked arithmetic overflow.

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

The original AVX linear update uses two overlapping masked loads before
each descending write. Its slice theorem gives the exact GF64 linear
coefficient update. The finite-heap theorem composes the checked
load and store contracts for every block, including the short block,
and preserves every byte outside the admitted slice.

The original AVX-512 Horner kernel and both wrappers check the complete
reverse coefficient fold in each lane, the empty-input zero fill, and
the final short masked chunk. Its allocated proof preserves every
byte outside the output and keeps the shared point view valid.
The existing scoped translator variant applies to the exact inner
kernel capture. The two wrapper captures use stock Aeneas.

Run the complete gate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
