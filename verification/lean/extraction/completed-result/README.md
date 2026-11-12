# Checked original completed row result

The projected declarations are the original `RowResult` and original
`Execution::completed_result`. Charon's exact source capture is pinned.
The stock recapture matches it after normalizing the destination path.

Stock Aeneas duplicates the ten inner mutable IDs when it reborrows
the frozen shared `RowWorkspace` before the result switch. Its borrow
invariant rejects the duplicate IDs. The included patch keeps that one
frozen input loan across the exact original switch spans. The guard
requires the flag, checked mode, input abstraction, matching workspace
ADT and all ten concrete nested mutable borrow shapes. Other loans
follow the stock reborrow path, and the stock invariants remain enabled.

The controls cover stock, flag-off and unchecked rejection, an exact
checked replay, wrong switch span and wrong workspace rejection, and
byte-identical unrelated execution verification. A fresh pinned build
also produces byte-identical output with `-strict-joins`. The projector
checks the original Rust signatures, the shared return lifetime, both
shared reads of the roots slot, and the exact generated declarations.

```sh
python3 verification/lean/extraction/completed-result/project.py
python3 verification/lean/extraction/completed-result/scope_controls.py \
  --stock "$stock_aeneas" --patched "$patched_aeneas" \
  --capture verification/lean/extraction/completed-result/arithmetic.llbc \
  --expected verification/lean/extraction/completed-result/Arithmetic \
  --compatibility verification/lean/extraction/execution-verify \
  --destination "$new_replay_directory"
```

`BulksketchBridge.CompletedResult.native_completed_result` proves the
returned error, decode failure, equality result and exact shared roots
prefix for every execution state and slice size. It also proves the
running-state and invalid-prefix panic paths. The decoded case includes
a zero-length roots prefix when the budget accounts for original zero.
