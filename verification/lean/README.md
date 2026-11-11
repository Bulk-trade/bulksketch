# Native Bulksketch Lean 4 proofs

This directory verifies native Bulksketch at reviewed source revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. Proof-only commits may change Git HEAD;
verification checks the exact native source and build-input fingerprints against
the frozen inventory. Native Rust remains the implementation.

The scope is `src/` with production configurations, including portable and x86
backends. The oracle, Minisketch, its bindings, and test-only implementations are
excluded. The initial inventory retains 344 executable source declarations and
532 declarations in total. Compiler-expanded bodies and complete per-item
contracts remain open, so no implementation-coverage percentage is claimed.

## End-to-end Portable decoder

We prove that two valid equal-shape in-memory `FrozenSketch` values representing
finite sets `A` and `B` reconcile to exactly `A △ B`. The returned IDs have no
duplicates. The result covers empty differences and changed membership of ID
zero.

The principal statement is
[`ActualPortableFrozenSketchEndToEnd`](bridge/BulksketchBridge/PortableSketchEndToEnd.lean),
proved by `portable_frozen_sketch_end_to_end`. Its row-level statement is
[`ActualPortableRowEndToEnd`](bridge/BulksketchBridge/PortableRowEndToEnd.lean),
proved by `portable_row_end_to_end`.

### Assumptions

- **Valid input representation.**
  [`ValidFrozenSketch`](bridge/BulksketchBridge/PortableFrozenSketchBoundary.lean)
  states that the original flattened syndrome storage has the shape's required
  length, the bucket count and every capacity are positive, and the stored odd
  syndromes correctly encode its modulo-routed ID set. Zero-word storage is
  nonempty, and the low bit of its first word records membership of ID zero.
  Both inputs have the same shape.
- **Capacity and output bounds.** Each bucket has capacity `c` in `1..65535`.
  Its true symmetric difference has at most `β` IDs and `β ≤ c`. If the zero
  membership bit differs, the row budget reserves one of those output slots
  for zero. The remaining budget bounds the nonzero support.
- **Admitted scratch.** Each row workspace satisfies
  [`WorkspaceAdmission.Admitted`](bridge/BulksketchBridge/WorkspaceAdmissionSpec.lean),
  including all required slice lengths and checked arithmetic bounds.
- **Sufficient work.** Each row starts with an unexhausted meter whose remaining
  allowance is at least
  [`rowWork`](bridge/BulksketchBridge/PortableRowEndToEnd.lean). The proof derives
  successful payment of reconstruction, BM, candidate evaluation, deflation,
  root traversal, verification, and canonicalization from this reserve.

### Checked scope

The row proof binds calls to the original Portable XOR, `BinaryDecoder::begin`,
and `Execution::finish` in the translated Rust implementation. It uses the
ordinary Portable GF64 route with empty candidate hints and derives the honest
locator and traversal conditions internally. The whole-sketch theorem applies
that result to the original frozen payload's bucket views and assembles the
returned IDs in bucket order. It also proves that the original `bucket_for`
routes each recovered ID to its output bucket.

Bucket views, the interpretation of the separate zero bit, and concatenation
are Lean adapters. Workspaces and meters are supplied per row. The connection
to Rust uses the pinned Charon/Aeneas translations and recorded standard-library
models described below.

### Verification record

Proof checkpoint `19e6250e35763c15ac2c7558dc362bb14c792bea` passed all six gates
of `scripts/verify_all.py`. The check matched 563 frozen statements, audited
their transitive axioms, and replayed the exported terms through Lean's kernel
and independent Nanoda. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The native release suite passed 139 tests
against the source pin recorded above.

From this directory, reproduce the checks with

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```

## Checked milestone

| Area | Result | Source relationship |
| --- | --- | --- |
| GF64 reduction | Universal division certificate for every 128-bit input, unique bounded quotient/remainder and XOR-linearity | Actual generated reduction using the actual extracted Gf64 dictionary; the generic BITS=64 contract is also retained |
| Raw multiplication | Full 128-bit GF(2) coefficient convolution, degree at most 126, exact nibble table and accumulator prefixes | Both original generated loops terminate normally; subtraction, reads/writes, shifts, casts and output splitting checked |
| Bit spreading and raw square | Exact coefficient placement and XOR-linearity for every 64-bit input | Actual generated spread; raw-square model and actual Gf64 square compose with reduction |
| Repeated squaring | Exact normal output for every U64/U32 input pair, strengthened to unmodded polynomial-square iterations | Original modulo-count contract retained; universal word-period theorem justifies the stronger endpoint |
| Period and modulus | Every word returns after 64 squarings; all natural iteration counts reduce modulo 64; exact `Polynomial (ZMod 2)` modulus is irreducible | Checked basis/linearity proof and polynomial square/Bézout/factor-degree certificates; quotient representation is proved separately below |
| Trace and quadratic maps | Complete 64-conjugate trace, all row/chunk identities, trace-zero solvability and normalized uniqueness | Actual source trace/canonical trace, row selector, 16-chunk value loop and solver refine the universal word models |
| Quotient field and algebra trace | Bijective polynomial-basis interpretation in Mathlib's exact irreducible quotient; multiplication, square, field laws and `Algebra.trace` transport | Existing native reduction/multiplication/square/Frobenius/trace endpoints strengthened in place; entire trace byte bounded by one |
| Inversion | Original chain, captured-square loop and all bounds; exact represented field inverse for nonzero input and `None` for zero | Actual three scalar inversion functions and Portable inverse; enclosing wrappers use the named checks-enabled reviewed frontend variant |
| Portable and const-square source | All eight Portable arithmetic methods; original x86-visible const-square with two 64-step loops and full byte output | Exact generated bodies and shared dependencies retained; no table/lookup or ISA execution credit |
| Work accounting | Exact finite-word overflow, boundary, failure and sequence accounting | UInt64 specification with actual-generated-body refinements below |
| `WorkMeter::new`, `charge` and `used` | Exact normal return, Rust result, final state and observed value for every generated state/amount | Unedited pinned Charon/Aeneas output, under the recorded runtime/compiler trust boundary |

The bridge now has 227 original Aeneas generated-body refinements under
their recorded contracts. Five source-linked LLBC execution contracts are
checked separately. The latest checkpoint covers the original root stage
dispatcher, Dense div/rem, factor division, affine enumeration
completeness, native affine-multiple termination and minimality, the full GF64
solve-map fibers and paid affine preparation, and fixed-stride pending
factor frames with degree conservation. The paid affine GCD step either
selects a proper division or retains every factor root in a smaller coset.
The original capacity-18 AVX packer and encoder and the insertion-base
lookup and generator have checked body refinements. The exact static
initializer supplies the lookup's field values. The AVX heap proofs cover
the captured masked reads and writes. The original GF64 affine predictor
and preference are checked through the traversal entry. The original
deflation stage checks both return paths through traversal start, and
the paid trace split test accepts every admitted split simple factor.
The candidate entry and Dense evaluation delegate have checked original
bodies. The native trace, affine splitter and GCD stages preserve the
returned coefficient and scratch frames between stages. The AVX
capacity-18 insertion, horizontal XOR, public GF64 insertion selector,
and complete free dispatcher have original-body refinements. The stock
decoder driver commits exact source state, progress, work and error
frames. The native candidate and deflation driver calls establish the
initial residual traversal product, and paid affine enumeration emits
the complete active factor. The original completed-result wrapper
returns the exact verified root slice. The local traversal proofs
preserve the represented locator product at division and emission.
The original shared candidate normalizer and modulo bucket selector
establish distinct nonzero candidate slices. The original canonicalizer
checks the sort boundary, work charge and root validation. The original
finish loop consumes a finite native driver trace, composes workspace
writebacks, and returns the exact terminal result. The honest BM guard
accepts the exact support locator, and the native candidate and
deflation calls establish the full initial traversal invariant.
The accelerated AVX recurrence checks every active lane and rejects
the first mismatched block. Its exact update and continuation bind to
the rebuilt verifier. Every admitted GF64 degree uses the original
AVX tile seed, PCLMUL XMM seed, or Portable seed, with the exact locator and continuation
callbacks and the recorded backend and masked-memory contracts.
The original row initializer and restart preserve the exact counter,
probe and stage setup. The affine preparation stage establishes the
first splitter or enumeration invariant under its admitted workspace.
Canonicalization returns the exact sorted roots under the terminal
locator-product and charge premises. The end-to-end Portable theorem above
closes the plain non-affine traversal and its work bound. Other decoder routes
and the remaining native implementation contracts have further obligations.
The checked row-local normalizer returns each row's exact sorted,
distinct, nonzero candidate slice under the admitted scratch bounds.
The original row dispatch preserves its backend tag and exact result
frame. The default wire difference checks every little-endian word
and the original guard results. The publication constructor, ordered
write, error latch and finalizer return exact storage and report views.
The original root budget bounds every proper binary factor tree, and
the V1 row budget uses the recorded checked sum-cost fold contract. The original AVX scale,
square and block update have checked finite-heap effects under the
admitted separated byte views.

The [core proofs](BulksketchProofs.lean) and [generated-body bridge](bridge/README.md)
use frozen proposition definitions, transitive axiom audits and exported-term
replay through Lean and independent Nanoda. The only permitted axioms are
`propext`, `Quot.sound` and `Classical.choice`. The current core and bridge use
all three. No admitted application-correctness or native
evaluation axioms discharge an obligation.

[RAW_MULTIPLICATION.md](RAW_MULTIPLICATION.md) explains the independent product,
both source-loop invariants, every bound and the final composition in detail.
[FIELD_ALGEBRA.md](FIELD_ALGEBRA.md) explains the exact modulus theorem, universal
period, table certificates and normalized quadratic solver semantics.
[QUOTIENT_FIELD.md](QUOTIENT_FIELD.md) explains the polynomial representation,
actual algebra trace, source inversion chain and remaining enclosing-wrapper gap.
[NATIVE_COVERAGE.md](NATIVE_COVERAGE.md) closes that wrapper gap under a named
reviewed frontend variant and explains the Portable and const-square proofs.
[FROBENIUS_TABLES.md](FROBENIUS_TABLES.md) records the table, lookup and slice checkpoint.
[SLICE_NORMALIZATION.md](SLICE_NORMALIZATION.md) records the mutable Zip and Dense proofs.
[RECONCILIATION.md](RECONCILIATION.md) records decoder dispatch, wire sizing and reconciliation.
[NATIVE_VERIFIER.md](NATIVE_VERIFIER.md) records the rebuilt verifier and Dense multiplication extraction.
[DENSE_PRODUCT.md](DENSE_PRODUCT.md) records the full Dense product, Portable Horner and direct two-root checkpoint.
[X86_REGISTER_MEMORY.md](X86_REGISTER_MEMORY.md) records the native x86 register kernels and pure masked-memory boundary.
[NATIVE_STATEFUL.md](NATIVE_STATEFUL.md) records the stateful LLBC contracts, accelerated field maps and cubic helper.
[NATIVE_CALLER_CHAINS.md](NATIVE_CALLER_CHAINS.md) records the x86 caller and native certificate checkpoint.
[NATIVE_RECONSTRUCTION.md](NATIVE_RECONSTRUCTION.md) records the original reconstruction stage, pricing and workspace admission.
[NATIVE_QUARTIC.md](NATIVE_QUARTIC.md) records the original affine and general quartic and candidate solve frames.
[NATIVE_CLOSED_LEAF.md](NATIVE_CLOSED_LEAF.md) records closed-leaf certification, accepted advance, and Newton normalization.
[NATIVE_NEWTON_GUARD.md](NATIVE_NEWTON_GUARD.md) records the original guard, residual loop and field recurrence proofs.
[NATIVE_BM_DEGREE_PROBE.md](NATIVE_BM_DEGREE_PROBE.md) records the admitted DegreeProbe stages and original BM subloop and branch proofs.

[NATIVE_BM_LOCATOR.md](NATIVE_BM_LOCATOR.md) records the original BM locator, root setup and small leaf, and verification-stage composition.

[NATIVE_DENSE_REDUCER.md](NATIVE_DENSE_REDUCER.md) records the original Dense reducer, trace stage and finite-address memory proofs.

[NATIVE_DENSE_DIVISION.md](NATIVE_DENSE_DIVISION.md) records the original exact-division and GCD wrappers, descending division model and accelerated square.

[NATIVE_ROOT_RUN.md](NATIVE_ROOT_RUN.md) records the original root dispatcher, factor division, affine splitter, and AVX square heap effects.

The [coverage ledger](audit/coverage.json) keeps every native item in scope,
including unsupported and unproved items. Related mathematical model evidence
and actual-generated-body refinement evidence have separate fields. Conservative
full native-contract statuses remain unproved until their remaining links close.

## Check the proofs

Install [elan](https://github.com/leanprover/elan), Python 3 and Rust toolchain
`1.96.1`. The Lean toolchain is pinned to `4.35.0`; its distribution must include
`leanexport`, `leanchecker` and `nanoda_bin`. The verifier fails if a checker is
missing.

From this directory, check the dependency-free core and negative policy fixtures:

```sh
python3 scripts/verify.py
python3 scripts/check_negative_fixtures.py
```

To include the actual-generated-body bridge, fetch its exact Lean runtime and
Mathlib dependencies, then run the combined check:

```sh
python3 tooling/setup_lean_runtime.py
python3 scripts/verify_all.py
```

The runtime setup clones only the pinned Aeneas source and its pinned Lean
dependencies. It does not install OCaml or build the Rust extractor. It disables
Mathlib's automatic full-cache update hook and requests cache artifacts only for
the explicit imports used by the runtime and native proofs, including the pinned
Mathlib finite-field modules. Setup/build caches are ignored by Git.

`verify_all.py` fails closed across core checking, bridge checking and negative
fixtures. It checks frozen endpoint propositions, exact source/body hashes and
axiom closures, then replays exported proofs in both kernels. The bridge uses a
small source-pinned loader for Lean 4.35's implicit string-dependency scheduling
gap, described in the [bridge checking notes](bridge/README.md). It uses the
unchanged parser and kernel and leaves the original proof export untouched.
The negative
fixtures confirm rejection of an application axiom and replacement of an unused
challenged theorem by a same-type axiom. Generated results and logs are written
under `audit/results/` and `bridge/audit/results/`.

The replay-loader fixtures additionally reject a malformed actual project proof,
conflicting preloaded declarations, unsafe/partial declarations, a valid extra
prelude declaration, and forbidden axioms in either input. A prelude may reorder
only an exact subset of the original export; it cannot extend the environment.

Every declaration projection retains original bodies byte for byte and checks
shared types and dictionaries against the larger arithmetic extraction. Seventy-two
mutation checks exercise source and runtime provenance in ordinary and optimized
Python. The runtime inventory records scoped value models for mutable slice Zip,
shared-slice reverse position and Option map-or. The three enclosing inverse
bodies require the named reviewed frontend variant with invariant checks.

These are controlled-source exact-type checks and independent proof-term replay.
Sandboxed Linux Comparator validation is a separate, remaining integrity gate.
Run native regression tests from the repository root with
`cargo +1.96.1 test --release --locked -p bulksketch`. This milestone includes the
verification commands; an automated CI workflow is not part of this change.

## Specification and source integrity

- [Challenges.lean](BulksketchProofs/Challenges.lean),
  [SpreadChallenges.lean](BulksketchProofs/SpreadChallenges.lean) and the
  [bridge challenges](bridge/BulksketchBridge/Challenges.lean) define intended
  propositions without proof holes.
- [frozen-inputs.json](audit/frozen-inputs.json) and its bridge counterpart pin
  those meanings, source descriptors and validator code. Intentional changes
  require an explicit review record; proof search must not silently weaken them.
- [scope.json](scope.json) records the reviewed native content, exclusions and
  axiom policy. A proof-only commit is allowed; a changed native body or build
  input is rejected until its source contract is reviewed.
- [source-linkage.json](bridge/source-linkage.json) ties the generated bridge to
  source spans, IR/body hashes and byte-identical generated application files.
- [obligations.json](bridge/obligations.json) maps source items and generated files
  to exact challenge/theorem pairs. The bridge verifier reconciles it with both
  the Lean audit and coverage ledger before reporting any functional refinement.

The bridge supplies concrete models for `Option::is_none_or`, `usize.trailing_zeros` and owned array
iteration. For the Option operation, None returns true and Some invokes the closure;
array iteration preserves the remaining value sequence and consumes its head.
Trailing-zero counting models every word, including zero and both pointer widths;
its exact count/bounds/least-set-bit properties are checked, including the table
caller's shift below four. All six new primitive-property theorems are exported.
Their Rust standard-library correspondence, including ownership/drop behavior,
is an explicit trusted boundary. The GF64 reduction theorem does not traverse
the generic fallback that contains array iteration; that fallback remains intact.
Charon/Aeneas frontend correctness, extraction-versus-production compiler
correspondence, allocator/runtime, intrinsic lowering and machine semantics also
remain separately declared assumptions. These proofs do not verify the compiler
or the entire Rust standard library.

Field maps reuse general checked conversions and add an exact population-count
model. The pinned runtime's integer-conversion error/Debug model erases diagnostic
detail. Native endpoint proofs establish inner `Ok` before every `expect`, and
independence from all Debug dictionaries is checked. Rust formatting correctness
is outside these claims.

## Regenerate source-derived artifacts

`python3 extraction/regenerate.py` reruns the small locked Rust/Syn AST utility
against the reviewed source fingerprints. It rejects unsupported syntax and
preserves the parsed XOR/shift expression. The generated expression is a model
artifact; its mathematical proof is not a theorem proving the translator correct.

The committed WorkMeter and arithmetic IR/generated Lean record actual extraction.
The IR retains historical build-path metadata; proof checking resolves paths
from this checkout and does not execute those historical paths. Regenerating
these actual Rust-to-LLBC-to-Lean artifacts requires the exact
[tool pins and recipe](extraction/README.md), separately from checking the
committed proofs. Generated application bodies must not be hand-edited.

## Remaining work toward full native coverage

The full-crate attempt remains incomplete: the Charon artifact reports errors
around associated iterator types, and full Aeneas translation encounters
associated-type, function-pointer, lifetime and loop limitations. They are proof
tooling gaps, not completed obligations or demonstrated library defects.

The core sketch mathematics and the ordinary no-hint Portable route have the
end-to-end result stated above. Broader verification work includes the public
constructors and updates that establish input validity, parsing and request
admission, the shared job loop and aggregate request work, candidate hints and
probe paths, V3 affine and closed-form composition, and accelerated backend
execution. Physical memory provenance and compiler-to-ISA correspondence remain
part of that broader scope.
