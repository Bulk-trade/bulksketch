# Original closed leaf and traversal helpers

Pinned Charon selects the original `Roots::closed_leaf` on x86-64 Darwin
with `deg34::solve` and `deg34::certificate` opaque. Both calls resolve
to their existing verified application declarations in the active projection.
Stock pinned Aeneas emits the complete selected body with `-checks
-sequential`. The exact declaration projector checks all six retained
declarations, the embedded Rust source, the reused types, and the existing
WorkSchedule and WorkMeter bodies.

`ClosedLeafAdvance.stage_refines` checks dispatch for every degree and
closed-form flag. `ClosedLeafAdvance.charge_refines` composes the original
pricing result with the verified meter frame, preserving the input meter
on a pricing error. `ClosedLeafAdvance.advance_refines` covers the empty
stack and every admitted pending frame, including the affine saved-base
index. It checks the restored coefficient prefix, the remaining workspace
fields, the updated traversal state, the next stage, and the returned
identity continuation.

```sh
python3 verification/lean/extraction/closed-leaf/project.py
cd verification/lean/bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.ClosedLeafAdvance
```
