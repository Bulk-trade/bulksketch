# Enclosing inversion, Portable arithmetic and const-square proofs

The associated verification record contains 26 source-body refinements. The
[Frobenius and slice proofs](FROBENIUS_TABLES.md) have a recorded total of 32.

These proofs use native source revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6` and its unchanged build inputs.
The component record contains 26 distinct generated-body functional refinements under the stated
translation/runtime/compiler/machine boundary. All 344 native executable
obligations and the preliminary 532-declaration inventory remain in scope.
Complete native coverage remains false; no percentage is claimed.

## The original enclosing inversion wrappers

[InverseUsing.lean](bridge/BulksketchBridge/InverseUsing.lean) proves the actual
generated captured-square closure, `maps::inverse_using`, and `maps::inverse`.
The captured callback loop admits every U32 power, including its maximum. Its
invariant preserves the range end and the complete repeated-square value; its
remaining range length strictly decreases. The active range discharges the
increment bound, and the terminal iterator returns before invoking a callback.

The generic wrapper has explicit universal equality of its multiplication and
square callbacks to the already verified native arithmetic. The closure itself
supplies the proved Frobenius callback to the original inversion-chain proof.
The outer `inverse` uses the actual generated native function-item dictionaries
and has no callback premise. Every U64 input returns normally: `None` exactly
for zero, otherwise the unique word representing Mathlib's field inverse.

These bodies use a named, pinned frontend variant. They do not use a new
application closure model, a successful-source-call premise, or an inverse axiom.
The [strict projection](extraction/inverse-wrappers/project.py) retains 22
original generated functions/helpers/dictionaries and one closure type alias
byte for byte. Common declarations are checked against the earlier original
extractions. Only the two enclosing handwritten functions add source-body credit.

## The checked Aeneas variant

The original pinned extractor and its earlier failure evidence are retained.
The variant is built separately from that same base with the versioned
[patch](tooling/aeneas-loop-capture/loop-capture.patch).

Its first change preserves an existing frozen immutable capture graph instead
of copying it into a fresh endable abstraction. Eligibility follows every
shared-borrow edge, requires frozen owners, rejects cycles and mutable/reserved
borrows, and permits only concrete values or opaque type-variable leaves.
Expandable symbolic referents remain on the conservative path. The existing
nested-loan collapse guard remains unchanged.

This case is enabled only with `-checks`. The existing join/fixed-point matcher
must verify unchanged frozen abstractions and identifiers. Unchecked extraction
still rejects the original capture case. A separate fix retains phantom generic
dependencies from actual loop signature input types; it does not skip type
annotations or invent a missing substitution.

The committed [receipt](tooling/aeneas-loop-capture/receipt.json) records baseline
and patched outcomes, alias/indirect-graph controls, an unchecked rejection, Rust
borrow-checker rejections, value tests and exact original inverse regeneration.
The [analysis](audit/aeneas-capture-analysis.md) discusses the
eligibility and matcher invariants, the generic-parameter fix and its limits.
This frontend remains an explicit trust boundary, not a Lean theorem of
translator or compiler soundness.

Ordinary proof verification requires the pinned base, exact patch, mandatory
check flags, original LLBC and generated hashes, complete regression matrix and
unchanged guard. It dry-checks patch applicability without modifying the original
runtime. Rebuilding OCaml and rerunning the optional extractor suite are separate
from checking the committed Lean proofs. The original Lean runtime remains clean
at its existing source pin.

## Eight original Portable arithmetic methods

[Portable.lean](bridge/BulksketchBridge/Portable.lean) composes seven original
forwarding bodies with the checked source arithmetic: multiplication, square,
Frobenius, trace, quadratic solving, raw multiplication and reduction. Every
native-width input is admitted. Contracts retain complete outputs and genuine
quotient-field meaning. Trace bounds the entire returned byte by one; quadratic
solutions have the fixed free coordinate and uniqueness among normalized field
roots.

[PortableInverse.lean](bridge/BulksketchBridge/PortableInverse.lean) adds the
original inverse forwarder with a callback-free field-inverse result. The seven
other methods use the unchanged pinned extractor; inverse uses the named checked
variant. Strict projectors validate all 43 or 51 shared declarations respectively.
No new runtime models are introduced.

## The original x86-visible const square

[FrobeniusConst.lean](bridge/BulksketchBridge/FrobeniusConst.lean) proves the actual
`field::frobenius::square`, extracted from the unchanged production source for
`x86_64-apple-darwin` with the unmodified pinned tools. This is a distinct body
from the previously proved `gf64::square`.

The first original 64-step loop places each input coefficient at its even
polynomial degree, through degree 126. The second loop decrements before
inspection, cancelling degrees 127 through 64. An invariant tracks the exact
accumulated full modulus multiple and already cleared upper coefficients for
every 128-bit input. Canonical remainder uniqueness connects this long division
to the earlier reduction specification. All I32 comparisons, increments,
doubling, subtractions and shifts are checked. The original eight array reads
are in bounds; little-endian reconstruction preserves every output bit.

The whole generated file, including both loop bodies/helpers, is byte-identical
to its original extraction. Those helpers are not extra source functions. This
does not grant table-initializer, lookup, accelerated-backend or ISA execution
coverage. Cross-target proof extraction is distinct from executing x86 code on
the Mac.

## Recorded verification results

The associated verification record reports `python3 scripts/verify_all.py`
checking 98 exact frozen propositions, transitive axiom closures, exact source/projection
linkage, Lean kernel replay and independent Nanoda on the original export. Only
`propext`, `Quot.sound` and `Classical.choice` are allowed. Replay caps are
unchanged. Source-projection mutations are tested in ordinary and optimized
Python; the existing application-axiom and replay-loader negatives remain.
The variant policy suite executes the actual validator gates with isolated
receipt data: three valid contexts pass and sixteen malformed contexts are
rejected, including empty artifact lists and hidden frontend attribution.

All 139 native release regression tests passed on the unchanged Rust source.
There is no native runtime change or claimed speedup. Historical performance
comparisons are described in the repository README.

The [Frobenius-table](FROBENIUS_TABLES.md), [slice](SLICE_NORMALIZATION.md) and
[decoder](README.md) documentation describe the related proofs. Public
state/resource/ownership contracts, accelerated end-to-end execution and
compiler-expanded closure are outside this component record. The original
source inventory is retained throughout. Replacement Lean decoders, test-only
implementations and Bulk consensus are excluded.
