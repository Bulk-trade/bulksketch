# Checked original row finish

The original `RowExecution::finish` repeatedly calls the original
`next_stage` and `run_next`, propagating the first Rust error. It calls
`completed_result` after a normal loop exit and returns its shared roots
view when the row was decoded.

The stock early-return prepass moves that final shared-result call into
the loop's normal break. The original checked capture then fails on the
nested shared borrow in the loop output. The scoped patch keeps both
original return conversions outside the loop, transporting a Boolean
normal/error tag and the borrow-free residual through the breaks.
The normal placeholder residual is unused. The actual error residual,
workspace frame, and backward callback are carried in source order.

The scope checks the exact structured finish method, source span,
original loop shape, next-stage and step calls, switch branch roles,
original error projection, and residual conversion. All ordinary
interpreter checks remain active. The projector pins the original
LLBC, both tool commits, exact generated output, shared lifetimes and
callee signatures. A fresh source build produces identical output in
checked and strict-join replay. The wrong-site and same-type
wrong-residual controls reject, and the unrelated original
`run_next` capture emits identical bytes with the flag enabled.

```sh
python3 verification/lean/extraction/native-finish/project.py
python3 verification/lean/extraction/native-finish/finish_controls.py \
  --stock "$stock_aeneas" --patched "$patched_aeneas" \
  --capture verification/lean/extraction/native-finish/arithmetic.llbc \
  --expected verification/lean/extraction/native-finish/Arithmetic \
  --compatibility verification/lean/extraction/native-driver/run-next \
  --destination "$new_replay_directory"
```

`BulksketchBridge.ExecutionFinish.native_finish` proves the exact
native return for a bounded certificate of original `run_next`
transitions. The loop and wrapper preserve the original stopping
condition, early Rust error, terminal completed result, final meter,
and ordered composition of the workspace callbacks.
