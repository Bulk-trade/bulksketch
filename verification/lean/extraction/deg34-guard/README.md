# Original Newton guard extraction

The pinned Charon selector is `bulksketch::decode::deg34::guard` with a
transparent application body on x86-64 Darwin. The projection retains
all thirteen original declarations. It uses the existing shared field
and kernel types and the checked `usize::trailing_zeros` binding.

The nested-slice retry extends the previously checked scalar-array
extractor. Its scope is the continuation-free fixed-point list join of
a loop. When both contexts hold the same immediate mutable borrow ID,
a mixed loan on its U64 slice child may request the stock retry to end
the shared loan. The shared payload must be a symbolic value of the
same slice type. The retry preserves the mutable continuation. Other
matcher modes use their original paths.

The full patch applies to the pinned Aeneas source. The delta applies to
the checked scalar-array extractor. The receipt records the checked
replay, pinned and unchecked rejections at the residual loop, ten OCaml
matcher controls, and the byte-identical quartic and normalization
controls. A fresh Charon extraction reproduced the frozen LLBC after
accounting for the output-file path. Checked replay reproduced all three
generated Lean files byte for byte.

The scope of the `project.py` check is source correspondence to the
retained generated declarations. The Lean guard proof separately checks
the writes and residual result. Six projector controls exercise altered
coefficient reads and writes, replay input, manifest, unchecked outcome,
and unrelated control output in independent fixtures.

```sh
python3 verification/lean/extraction/deg34-guard/project.py
PYTHONDONTWRITEBYTECODE=1 python3 -O verification/lean/extraction/deg34-guard/check_controls.py
cd verification/lean/bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build Arithmetic.NewtonGuardGenerated
```
