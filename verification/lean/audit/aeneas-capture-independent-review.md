# Independent review of checked Aeneas capture translation and source wrappers

Date: 2026-11-06. Native source pin: `0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.
Reviewer: `portable_proofs` agent. This review is independent of the agent who
implemented the translator patch and the root agent who authored InverseUsing.
The reviewer authored the Portable forwarding files; their discussion below is
self-review, not a claim of independent authorship.

## Result and limits

No blocking defect was found in the final reviewed narrow patch or the three
source-wrapper propositions. The former direct-only shared-value predicate was
not accepted: it did not follow captured borrow referents. The final patch
resolves that issue with a recursive frozen-owner check and requires enabled
sanity checks. The original collapse guard is byte-identical to the pinned
version. The old pinned runtime checkout remains clean and unchanged.

This is a bounded code/invariant and regression review under an explicit
frontend trust boundary. It does not prove Aeneas or Rust compiler correctness
in Lean. Successful extraction alone does not establish such correctness and
adds no native-body coverage credit. Native source and build inputs are unchanged.

## Immutable capture eligibility and loop matching

The new InterpJoin predicate follows each `VSharedBorrow` edge through the
existing loan-to-value map. Every traversed owner must already be frozen. An
acyclic shared-only concrete ADT/literal graph is admitted, with opaque `TVar`
symbolic leaves only. Missing owners, endable owners, cycles, mutable or reserved
borrows, loan values, bottom, scalar-symbolic values, and expandable symbolic
ADTs/references are rejected by the predicate and retain the original path.
Alias DAGs can share a node: the visited set is path-local, so a repeated sibling
reference is not mistaken for a cycle.

The original loan IDs, shared-borrow IDs and frozen abstractions are retained;
no new loan or region is fabricated, no abstraction is arbitrarily marked
frozen, and the unsupported nested-collapse guard is not removed. The branch
can execute only with `Config.sanity_checks` enabled by `-checks`.

The relevant existing safeguards were inspected directly:

- InterpLoopsFixedPoint computes fixed IDs from the original context.
- InterpMatchCtxs requires fixed abstractions to remain `equal_abs` with fixed
  identities; corresponding join checks remain enabled as well.
- InterpExpansion has no structural expansion for `TVar` leaves, unlike ADT and
  reference symbolic values. This is an existing representation property, not
  a new assumed callback result.
- Concrete field borrowing can still introduce loan structure. The enabled
  frozen-abstraction equality checks are material: a change to a fixed input
  must fail matching rather than silently becoming a loop constant.

These checks constrain the accepted state transition. The argument is not that
every Rust value behind a shared pointer is universally immutable; it is that
the admitted representation graph is retained and its original frozen context
must remain unchanged under the existing checked loop matcher. Generic trait
calls that expose shared references are exercised by `captured_borrow_result`.

## Signature generic parameters

The separate annotation failure was traced to filtering generic parameters from
only the normalized loop expression while original closure input types still
mentioned phantom type parameters. The change collects variables from actual
constant/formal input types before the existing trait-clause dependency fixed
point. Both loop-helper construction call sites pass their actual input types.
It retains necessary parameters and their existing indices/filters; it does
not postulate a type equality or alter native operations. The phantom-callback
regression and the original inverse extraction both complete with the change.

## Regression evidence and independent reruns

The reviewed runner uses checks-enabled extraction and validates complete
non-partial output. Its matrix records captured callback, aliased capture,
phantom callback and returned-borrow positives; an unchanged ordinary shared
loop; three unchanged indirect graph controls; a no-checks rejection; two Rust
borrow-checker rejection controls; Rust value regressions; and the original
inverse LLBC regeneration. The indirect graph controls are observed unchanged
acceptance/rejection tests, not a formal proof of all possible graph shapes.
Rust E0502 controls are explicitly Rust compiler controls, not translator proofs.

The reviewer independently reran four cases using the exact reviewed binary:

| Case | Observed status |
| --- | --- |
| Original captured callback, pinned baseline with checks | Exact old collapse guard rejected it |
| Generic reader returning `&u64`, patched with checks | Complete extraction succeeded |
| Captured callback, patched without checks | Exact old collapse guard still rejected it |
| Original BulkSketch inverse LLBC, patched with checks | Complete output exactly matches the retained original-source Funs/Types files |

Independent commands, timings and log fingerprints are preserved outside Git at
`/workspace/bulk/bulksketch-proof-tools/capture-independent-review/receipt.json`.
The reviewed matrix is committed separately in the translator receipt. The
patched binary fingerprint also agrees with the Portable inverse extraction.

## Source and mathematical endpoint review

`capturedSquareReturnsEveryIteration` quantifies every native U32 endpoint,
including its maximum. `captured_loop_refines` uses the actual range iterator's
proved normal result, preserves its end value, and strictly decreases the
remaining length on every active step. The active range proves that increment
cannot overflow. Both empty and nonempty ranges are covered. The postcondition
is full unmodded repeated squaring, not an assumed successful source return.

`actualInverseUsingReturnsFieldInverse` names universal equality of supplied
callbacks to the actual native multiplication/square bodies. The actual
generated closure supplies the proved Frobenius callback to the already proved
source inversion chain. `actualInverseReturnsFieldInverse` then discharges both
callback equalities through the actual generated native function-item
implementations; no callback premise remains in that endpoint. Its output uses
the earlier exact Mathlib inverse specification (`None` for zero, otherwise the
unique represented field inverse). No inverse law is assumed of the source.

The exact declaration projection retains the 22 generated function/helper/
dictionary declarations and one type alias verbatim, with every common type and
function checked against the previous original extraction. No opaque closure
model replaces the original body. Generated Fn helpers and the type alias are
not counted as extra handwritten native source functions.

The additional Portable inverse extraction uses the same reviewed binary and
both `-checks`/`-sequential`. Its single forwarding declaration is retained
verbatim; all 51 shared functions/dictionaries and shared types are checked.
Its callback-free endpoint composes with the actual source inverse endpoint.
The seven earlier Portable forwarding methods remain on the original pinned
extractor. Their exact challenge assignments, local builds and standard-axiom
closures were checked, with global independent replay owned by the root agent.

All 344 native executable obligations remain in scope. This review does not
establish complete native-contract closure or full implementation coverage.

## Reviewed hashes

Paths are relative to `verification/lean`.

| File | SHA-256 |
| --- | --- |
| `tooling/aeneas-loop-capture/loop-capture.patch` | `15ecb6d84c03d7ad68a384f10b153a1538474d813bacaeb27d4e79156cfbf111` |
| `tooling/aeneas-loop-capture/run.py` | `d7c058d5c76b5b58309b3c249cd93bdd524ace5503b155bf4d34992cabea1747` |
| `tooling/aeneas-loop-capture/receipt.json` | `1ccae604cfcf8b5587e16028e5351d6fcb9e5414bd5f1352e5ee26111a698bb6` |
| `bridge/BulksketchBridge/InverseUsingChallenges.lean` | `e5a7a24c61ae853775ee7c0266f49abecf120f1a0f5aa61e924d49c3f7827141` |
| `bridge/BulksketchBridge/InverseUsing.lean` | `0627aa030ae412b4b906d533e9d95f701dcad784aa0cf072d5ae6445432ea4f1` |
| `bridge/Arithmetic/InverseUsingTypes.lean` | `619fb7c67f9aa399df652f490893644a1cbcdce23748b885f5a93a38acad7235` |
| `bridge/Arithmetic/InverseUsingGenerated.lean` | `7c6ad32c606fe4779dc950fc6bc77b2631a36033eba170301eb0a5e12a0dfb46` |
| `extraction/inverse-wrappers/project.py` | `63e1514ea54745c244ce1819d810f1c79ecff59ad47c840d4bb605498309dfa7` |
| `bridge/BulksketchBridge/PortableInverseChallenges.lean` | `f03e0f23dd87626c7b6f8ae10ef8adfa6e0dd8d38ef0a079b860570bc1494a79` |
| `bridge/BulksketchBridge/PortableInverse.lean` | `5f66be4b17e9ed1f77c8c31ffd66405e99037fcb346b0bfabddcf79124c0ea7c` |
| `extraction/portable-inverse/project.py` | `1ab56ea02e2a6b2e4cd7e2cd94a01e94f0766c76a359268565551ccac82f4e9a` |
