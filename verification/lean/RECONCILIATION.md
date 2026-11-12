# Decoder dispatch and reconciliation

The [native verifier and Dense multiplication proofs](NATIVE_VERIFIER.md)
cover the related source kernels.

The checked source baseline remains `0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.
The coverage ledger retains all 344 executable native declarations. Each
generated-body credit names an original source span, an exact generated
declaration and a frozen proposition. Mathematical theorems carry zero
additional source-body credit.

## Native dispatch, recurrence and wire sizing

The original `product_counts` returns `None` for degree greater than capacity
or capacity greater than 65,535. For admitted dimensions, the proof bounds
every checked scalar operation and returns the exact raw-product and
including-reduction counts for both strategies. The complete tiles, four tail
cases, locator blocks and continuation ceiling follow the frozen natural
number specification. The pinned Rust core `div_ceil` is modeled by quotient,
remainder and checked increment. The proof uses its exact natural ceiling for
the denominator eight.

The original `use_rebuilt_lfsr` declines degrees at most two and rejected
dimensions. Otherwise it selects the rebuilt path exactly when both counts
are no greater and at least one is strictly smaller. The proof uses the
extracted derived equality for `ProductCounts`.

The original scalar default `BulkKernels::odd_recurrence_matches` checks every
continuation equation for a nonempty squared locator. The proof establishes
both loops, every indexing and subtraction bound, the raw XOR accumulator
in the field, and the first-mismatch return. It is parameterized by explicit
raw multiplication and reduction equations for the selected callback
dictionary. A separate composition theorem proves that this native
continuation accepts exactly when the whole odd row matches directly, given
the correct seed comparison and squared locator. The VPCLMUL512 override
and native seed/coefficient construction are outside this component record;
the [native verifier proofs](NATIVE_VERIFIER.md) describe their source contracts.

The original `record_bytes` returns the complete wire length
`24 + 2*buckets + 8*words + ceil(buckets/8)` exactly when the descriptor
and payload lengths fit `u32` and the total fits `usize`. The theorem
includes every modeled input pair and both modeled pointer widths. Shape
allocation and parser admission are separate obligations.

## GF64 reconciliation

- Characteristic two gives `S(2j) = S(j)^2`, so the first `c` odd words
  determine the positive power sums through exponent `2c`. The native
  reconstruction uses a zero sentinel at index zero.
- If two nonzero supports of size at most `c` agree on those odd words, their
  symmetric difference has at most `2c` elements and vanishing positive
  power sums. A Vandermonde system with each support word as its own nonzero
  weight forces that difference to be empty.
- The locator `L(z) = ∏ (1 + r z)` yields the odd recurrence by squaring its
  coefficients. Each root contributes a sequence with ratio `r²`, which
  satisfies this recurrence. Equality on the first `min(d,c)` words and
  the remaining recurrence equations is equivalent to full direct comparison.
- If a degree-`k` candidate fits a prefix of `N` positive power sums and
  `d+k ≤ N`, a weighted Vandermonde system forces it to vanish on each of the
  `d` roots. Consequently the exact support polynomial divides the candidate.
  A nonzero fit has degree at least `d`, and a monic fit of degree at most
  `d` equals the support polynomial.

These uniqueness and recurrence theorems supply the algebraic premises for
the native decoder. The [reconstruction](NATIVE_RECONSTRUCTION.md),
[Berlekamp–Massey locator](NATIVE_BM_LOCATOR.md), [root traversal](NATIVE_ROOT_RUN.md)
and [verification](NATIVE_VERIFIER.md) proofs establish the corresponding source
contracts. The [Portable theorem](README.md) composes the ordinary no-hint route,
including work bounds and zero-ID handling, under its stated input, capacity,
workspace and work-meter assumptions.

The original extraction record includes a failed reconstruction context join
at the in-place syndrome update. That diagnostic describes the specified
translator configuration; it does not describe the completed reconstruction
proofs linked above.

## Dense polynomial square

The checks-enabled shared expansion variant fixes the post-loop prefix read
and produces the original `Dense::square_into` extraction. The patch and
guard controls are documented with the translator. The original Dense
square body preserves the raw scratch and destination tail. It clears every
odd coefficient slot, writes each squared source coefficient to twice its original
index, and returns the exact normalized length. The normalized output
represents the square of the input polynomial over GF64. The frame theorem
also covers both buffer assertions and checked scalar overflow in the
generated model. Physical slice representability stays within the memory
boundary.

The recorded `Dense::mul_into` extraction reached a level-1 abstraction-lowering
guard when ending a nested shared loan from the final reduction Zip. Its shared
iterator had no emitted continuation, while the mutable destination had one.
The required lowering invariant is that the affected nested projectors are
entirely shared and their ending is erased. The same record includes a Portable
Horner context-join failure in the zipped outer loop. The
[Dense product and Horner proofs](DENSE_PRODUCT.md) document the pinned frontend
variants and complete function-body contracts.

The runtime bindings model standard-library value behavior. Source and
translator correspondence, memory and alias semantics, and machine ISA
contracts remain in the recorded trust boundary. The audit matches the
frozen propositions and replays their proof terms with both Lean and Nanoda.
