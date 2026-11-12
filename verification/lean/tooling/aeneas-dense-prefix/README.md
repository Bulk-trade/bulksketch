# Checked shared expansion owners

The `checked-shared-expansion-owner-v1` variant translates the original Dense
`square_into` body using a one-file patch to Aeneas
`ab34bd28458a08c150b7cbf1873e59af74588138`. Its extraction command enables
`-checks -sequential`. The isolated extractor builds against the pinned Charon
sources. The Lean runtime continues to use the clean base checkout.

## Diagnosis

After a mutable prefix loop, Rust borrows the updated destination prefix for
normalization. During expansion of that new shared reference, Aeneas visits a
borrow projector for the previous Zip iterator. That older projector carries a
loan from an ended ancestor. The empty-loans assertion ran before the walker
compared the projector owner with the expansion target.

A diagnostic-only build printed all three IDs before the original assertion.
The IDs are local to each symbolic execution.

| Source | New shared reference | Projector owner | Child loan |
| --- | ---: | ---: | ---: |
| Prefix Zip reproducer | 62 | 12 | 57 |
| Prefix stride reproducer | 66 | 15 | 60 |
| Original `mul_into` | 548 | 495 | 543 |
| Original `square_into` | 81 | 27 | 75 |

The same unconditional assertion was present in the generic borrow-projection
pass that follows the shared expansion. The patch makes both passes require an
empty loan payload for a matching owner. When checks are enabled, an unrelated
owner encountered during shared expansion keeps its payload and the visitor
continues through its children. The existing child guards still reject a target
hidden in a loan child. Non-shared expansions and unchecked runs retain the
original empty-loans requirement.

The checked translator and its source projection are part of the documented
extraction trust boundary. The Lean proof of the generated square body has its
own source linkage, challenge and independent replay checks.

## Regression controls

`run.py` extracts the included Rust fixtures with pinned Charon and checks both
original failures against the base extractor. The checked variant emits real
definitions for both prefix-read functions. The unchecked variant reproduces
their rejection. The Rust value test checks the updated prefix, preserved tail,
and the untouched odd positions in a stride traversal.

The OCaml fixture calls the public expansion routine with deliberately invalid
projector contexts. It checks rejection of matching owners with loan payloads
and targets inside unrelated loan children for both abstraction values and
continuation expressions. It also checks the original rejection for a
non-shared expansion encountering a nonempty unrelated payload. These five
controls exercise the existing interpreter guards directly.

The runner replays the preserved square-only LLBC and compares the complete
generated `Types.lean` and `Funs.lean` byte for byte. The input and raw output are
in `extraction/dense-square`, with the original Charon and Aeneas commands in
that directory's receipt. The variant receipt records the patch and tool
fingerprints, fixture sources, checked command and all control outcomes.

The combined `mul_into` and `square_into` extraction reaches a separate lowering
guard for `mul_into`. The trace ends level 1 of `Loop 5` at `abs@313`, whose
payload includes loan `s@543`. The guard in
`SymbolicToPureExpressions.ml:1288` currently accepts level 0. That lowering
remains open. The scoped square extraction exits successfully and provides the
only native artifact for this variant in the proof package.

The owner diagnostics and combined-extraction trace are local evidence under
`/workspace/bulk/bulksketch-proof-tools/dense-prefix-investigation/`.

## Reproduction

Apply `owner-guard.patch` in a separate checkout of the base Aeneas commit. Link
its `charon` directory to the pinned Charon sources. Build the `src` project in
the existing OCaml 5.3 environment and run the optional regression driver from
`verification/lean`.

```sh
opam exec --root=/workspace/bulk/bulksketch-proofs/tooling/opam-root \
  --switch=aeneas-5.3.0 -- dune build \
  --root /workspace/bulk/bulksketch-proof-tools/aeneas-dense-prefix/src -j 2

python3 tooling/aeneas-dense-prefix/run.py \
  --charon /workspace/bulk/bulksketch-proofs/tooling/charon/bin/charon \
  --baseline-aeneas /workspace/bulk/bulksketch-proofs/tooling/aeneas/src/_build/default/main.exe \
  --patched-aeneas /workspace/bulk/bulksketch-proof-tools/aeneas-dense-prefix/src/_build/default/main.exe \
  --patched-source /workspace/bulk/bulksketch-proof-tools/aeneas-dense-prefix \
  --opam-root /workspace/bulk/bulksketch-proofs/tooling/opam-root \
  --output /workspace/bulk/bulksketch-proof-tools/dense-prefix-investigation/regressions
```

The optional run writes fresh logs and a receipt. Ordinary Lean verification
checks the frozen receipt and source artifacts without building OCaml.
