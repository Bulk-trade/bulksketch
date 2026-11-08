# Checked matching of ended scalar loans

The `checked-ended-shared-scalar-v1` extractor is Aeneas
`ab34bd28458a08c150b7cbf1873e59af74588138` with one reviewed patch to
`src/interp/InterpMatchCtxs.ml`. The original Portable Horner body is the
only native extraction associated with this variant. The Lean runtime
comes from the clean pinned Aeneas checkout.

## Diagnosis and patch

The shared loan for the copied leading coefficient ends after
`split_last`. The remaining coefficient slice is still borrowed, so the
abstraction holds the ended scalar loan alongside the active shared
loan. At the outer Zip loop match, both contexts contain the same
`AEndedSharedLoan`. The generic loan dispatch has no case for that
constructor and reaches its recoverable fallback. The outer context
match then reports `Could not match the contexts` at
`InterpJoin.ml:1571`. A diagnostic build inspected the ignored child,
which the pretty printer displays as `_`. Its optional payload is the
same symbolic scalar as the ended loan metadata.

The patch admits a pair of these nodes in checked context matching.
It requires equal scalar values, including the exact symbolic identity
and type, and two ignored children of the scalar type. A child payload,
when present, must repeat the scalar exactly in each context. The
ordinary matchers still validate types and register the symbolic
mapping. The result retains the ended node and its child metadata.
The case creates no loans and discards no active child. Join and
collapse callers retain the original matcher mode. Context matching
without `-checks` retains the original rejection.

The variant and the standard-library correspondence used by the
scoped Lean runtime are part of the extraction trust boundary. The
Lean proof uses the original generated Horner declarations and the
checked model of the shared-slice reverse fold and mutable Zip frame.

## Replay

Apply `ended-shared-scalar.patch` in a separate checkout of the pinned
Aeneas commit. Link that checkout's `charon` directory to the pinned
Charon sources and build its `src` project with the same OCaml switch
as the clean pinned extractor. From `verification/lean`, run:

```sh
python3 tooling/aeneas-horner-match/run.py \
  --charon-source /Users/junbug/bulk/bulksketch-proofs/tooling/charon \
  --baseline-source /Users/junbug/bulk/bulksketch-proofs/tooling/aeneas \
  --patched-source /Users/junbug/bulk/bulksketch-proof-tools/aeneas-horner-match \
  --opam-root /Users/junbug/bulk/bulksketch-proofs/tooling/opam-root \
  --output /Users/junbug/bulk/bulksketch-proof-tools/horner-match-investigation/regressions
```

The runner checks the pinned revisions and exact diff. The Rust
reproducer fails at the original context guard on the baseline and
translates with checks on the variant. Its ordinary Zip control has
three byte-identical generated declarations. An unchecked run retains
the original guard. Synthetic OCaml contexts exercise exact scalar
matching and equivalence, distinct IDs or payloads, one-sided payloads,
nested child loans, nonscalar metadata, and unchecked rejection.
The original input produces all four frozen Lean artifacts byte for
byte on the variant and fails at the same guard on the baseline.
`receipt.json` records the test sources and exact commands.
