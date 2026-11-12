# Native rebuilt verifier and Dense multiplication checkpoint

This checkpoint precedes the [complete Dense multiplication and Portable Horner proofs](DENSE_PRODUCT.md).

The audit retains all 344 executable obligations from the frozen native
source revision. It now checks 46 original generated-body refinements.
This checkpoint adds the original rebuilt verifier, Portable insertion,
default encoder and affine linear evaluator. The Dense final reduction loop
and the composition theorems are recorded separately with zero additional
source-body credit.

## Rebuilt verifier

The locator begins as the zeroed degree-plus-one prefix with coefficient zero
set to one. The first loop enumerates the root slice. At root index `i` it
takes the first `i+2` words, applies the proved linear factor update and
restores the prefix. The spare slot is zero at each step, so the final
ascending polynomial is the exact product of the factors `1 + rX`.
The tail beyond the active locator window is preserved.

The verifier clears exactly `min(degree, capacity)` seed words and compares
them with the same-length prefix of the received odd row. Portable insertion
computes the seed as the sum of the odd powers of the candidate roots. The
original default encoder's singleton and batch paths compute that same fold.
On a seed mismatch the verifier returns false with the unsquared locator.
On a match it squares the nonconstant coefficients and passes the exact
squared locator to the scalar continuation. Both mutable scratch buffers
retain their inactive tails.

With distinct nonzero roots, valid scratch lengths and the specified
backend callback equalities, the original rebuilt verifier accepts exactly
when the entire odd row matches the candidate support. The Portable seed
composition supplies the seed theorem from the original insertion body.
Its locator and recurrence premises identify the original scalar defaults
and the previously checked GF64 arithmetic. The accelerated backend and
whole decoder still need separate composition.

The affine evaluator proof covers the original coefficient loop, every
checked read and increment, and the skip of the final square. For exact
GF64 arithmetic callbacks it evaluates the sum of coefficient `i` times
the input raised to `2^i`.

## Dense multiplication

The checked shared-loop erasure variant completes extraction of the original
Dense multiplication body and all three loops. It is cumulative with the
previous shared-owner fix. Erasure requires a checked level-one ending of
an already-ended Loop abstraction, a unit self call, an ignored abstraction
ID, no continuation, and a recursive check for mutable payloads in the owned
regions. The recorded controls include mutable children and continuation
metadata, the original failing parent translator, unchecked mode, and
byte-identical Dense square compatibility.

The final reduction loop proof covers equal-length destination and raw
prefixes, with a callback agreeing with native GF64 reduction. Applying
its returned continuation writes every remaining reduced coefficient to the
destination, preserves earlier destination words and retains the shared
raw slice before the incoming continuation. The two raw convolution loops,
outer scratch management and normalization still need proofs.

## Remaining extraction and proof gaps

Portable Horner's context matcher reaches two identical ended shared loans
from `split_last` and rejects the ended-loan pair in `InterpMatchCtxs.ml`.
The reconstruction experiment recovers the branch join and then reaches
the mandatory loop-backedge match. Native Berlekamp–Massey extraction still
fails while lowering early returns in its loop. These diagnostics carry no
source-body credit. Native reconstruction, locator fitting, root recovery,
work limits, accelerated verification, and compiler-expanded memory and ISA
contracts remain in scope.

The proof audit checks source hashes, generated declarations and explicit
callback and runtime boundaries. Physical pointer, alias and ISA
correspondence remain separate from the checked value models.
