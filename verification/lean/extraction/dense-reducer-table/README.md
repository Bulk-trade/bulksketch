# Original Dense square reducer table

The pinned Charon capture includes the original
`Dense::prepare_square_table` method and its modular shift callee.
The source commit and Rust bodies are unchanged. Stock Aeneas rejects
the original odd-degree conditional join at `dense.rs:176:8–178:9`.

The checked variant recognizes a pair of identical symbolic shared
`Option<&u64>` loans from the earlier monic guard. It requires the same
loan ID, the same symbolic payload, and no projection markers. It
recognizes the identical ignored shared child only when it is a
marker-free loan projector without consumed or borrowed children.
It uses the stock value, projector, loan and region maps for both
cases. The ordinary join matcher is unchanged. The gate requires the
explicit reducer flag, checked mode, and an original Dense reducer
source span. No new case covers a differing payload or a mutable loan.

The compiled projection retains the method, loop and loop body
verbatim. It imports the independently checked original
`times_x_mod` and its RangeTo dictionary. The scoped `last` and
`Option.eq` bindings model the two Rust standard-library calls in the
monic guard. Lean proves every table word and the final work-prefix
restoration from the original method under its native admissions and
the exact scale-XOR law. The loop writes the current row before the
two modular shifts for the following row and performs no final
unneeded shift.

The receipt records both byte-identical checked translations, stock,
flag-disabled and unchecked rejections at the original join, and the
byte-identical unrelated Portable XOR control. The three theorem
endpoints use only the permitted axioms.

## Replay

Build the pinned Aeneas sources in a separate checkout with the
included patch applied and their pinned Charon dependency. From
`verification/lean`, run:

```sh
python3 extraction/dense-reducer-table/replay.py \
  --patched-source /workspace/bulk/bulksketch-proof-tools/aeneas-dense-reducer-join \
  --output /workspace/bulk/bulksketch-proof-evidence-20261109-dense-reducer/replay-fresh
python3 extraction/dense-reducer-table/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.DenseReducerTable
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake env lean ../extraction/dense-reducer-table/Axioms.lean
```
