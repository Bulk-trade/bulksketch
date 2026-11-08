# Original Dense modular square

The original `Dense::square_mod_into` method and all six loop
declarations are retained verbatim. The capture uses the original
pinned Charon LLBC and a composition of three previously checked
Aeneas changes. The included patch contains the exact reducer
Option matcher, the shared-expansion owner check and the Dense
shared-only level-one erasure guard. The projector compares each
patch section byte for byte with those reviewed parts. Mutable
row and final-reduction writeback callbacks survive the lowering.

The checked original high-table row Zip and final reduction Zip are
definitionally equal to the independently proved convolution row
and reduction loops. The original outer accumulation has an exact
finite recurrence for the low coefficient write and the high table
row. The wrapper theorem checks the original modulus and width
guards, actual backend call, selected path, raw and output prefix
restoration and normalized length under its native admissions and
GF64 kernel equations. The accelerated kernel result remains a
premise of the wrapper theorem. The portable fallback performs
the complete proved scalar accumulation and reduction.

The receipt records a second byte-identical checked translation,
stock, flag-disabled and unchecked rejections at the original high
table branch join, and the byte-identical unrelated Portable XOR
control. All four checked theorem endpoints use only the permitted
axioms. No Rust or Cargo inputs change.

## Replay

Build the pinned Aeneas sources in a separate checkout with the
included cumulative patch and pinned Charon dependency. From
`verification/lean`, run:

```sh
python3 extraction/dense-reducer-square/replay.py \
  --patched-source /Users/junbug/bulk/bulksketch-proof-tools/aeneas-dense-reducer-square \
  --output /Users/junbug/bulk/bulksketch-proof-evidence-20261109-dense-reducer/dense-square-mod/replay-fresh
python3 extraction/dense-reducer-square/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.DenseReducerSquare
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake env lean ../extraction/dense-reducer-square/Axioms.lean
```
