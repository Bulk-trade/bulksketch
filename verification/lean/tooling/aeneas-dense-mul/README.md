# Checked erasure of shared loop endings

The `checked-shared-loop-erasure-v1` variant translates the complete original
Dense `mul_into` body with `-checks -sequential`. Its cumulative patch applies
to Aeneas `ab34bd28458a08c150b7cbf1873e59af74588138` and starts with the exact
previous Dense prefix owner patch. The additional change handles a symbolic
lowerer for a checked level-1 loop ending whose continuation erases to unit.

The final reduction Zip keeps separate abstractions for the mutable destination
and the shared raw-product iterator. The level-1 ending closes the shared
iterator's nested returned loan before its level-0 ending. The lowerer already
emits the mutable iterator's backward continuation and records the shared
iterator's unit continuation as erased. The original level-0 assertion also
ran on that erased shared ending.

The new branch requires the actual ended level marker, the existing erased
registration, the absence of a data continuation in the map, and a unit self
loop call. It inspects every symbolic projector and child payload type for
mutable borrows in the regions owned by the abstraction. The check includes
types in consumed and given-back metadata. Active nested projectors and
non-symbolic abstraction values fail this test. All other cases go through the
existing level-0 assertion and continuation handling.

The `owner-only` control reproduces the original lowering failure at line
1288. The checked run fully translates the same scoped LLBC and matches both
preserved generated files byte for byte. A square compatibility control matches
the previous square extraction. The unchecked control reaches the original
prefix owner guard. A separate OCaml executable exercises the erasure predicate
with one admitted shared context and twelve rejection cases. The mutable tests
include an otherwise shared outer projector whose consumed child type contains
an owned mutable borrow.

The original Charon command, pinned native source inputs, and raw artifacts are
recorded in `extraction/dense-mul/receipt.json`. The two final reduction loop
declarations are projected into `Arithmetic.DenseMulReductionGenerated` and
proved using the existing mutable Zip model. This endpoint establishes the
exhausted cursor and applied backward callback frame on equal length prefixes.
The convolution and complete source method are separate proof obligations.
The compiler change belongs to the documented translator trust boundary.

## Reproduction

Apply `shared-loop-erasure.patch` to a separate clean base checkout and link
its `charon` directory to the pinned Charon sources. Build the `src` project in
the existing OCaml 5.3 environment. Keep the owner-only checkout available for
the comparison. Run the optional regression from `verification/lean`.

```sh
opam exec --root=/Users/junbug/bulk/bulksketch-proofs/tooling/opam-root \
  --switch=aeneas-5.3.0 -- dune build \
  --root /Users/junbug/bulk/bulksketch-proof-tools/aeneas-dense-mul/src -j 2

python3 tooling/aeneas-dense-mul/run.py \
  --owner-source /Users/junbug/bulk/bulksketch-proof-tools/aeneas-dense-prefix \
  --patched-source /Users/junbug/bulk/bulksketch-proof-tools/aeneas-dense-mul \
  --opam-root /Users/junbug/bulk/bulksketch-proofs/tooling/opam-root \
  --output /Users/junbug/bulk/bulksketch-proof-tools/dense-mul-investigation/regressions
```

The optional run writes fresh logs and a receipt. Ordinary Lean verification
checks the frozen receipt and artifact bindings without rebuilding OCaml.
