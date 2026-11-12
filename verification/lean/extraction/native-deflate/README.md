# Checked original deflation extraction

The retained five declarations cover the unmodified `Execution::deflate`,
both loops and their bodies. Charon's source capture is byte-pinned. Its
fresh capture matches the original after normalizing the destination path.

Stock Aeneas rejects the outer return join while matching an opaque
successful `Roots::start` workspace against the rejection workspace.
The latter still holds the shared roots iterator loan. The single-file
variant checks the exact source span, `-checks`, explicit
`BULKSKETCH_DEFLATE=1`, workspace ADT, and sole loan in the roots slot.
It sends that loan through Aeneas's existing checked retry. All invariant
checks remain enabled.

`project.py` checks the capture, embedded Rust source, generated bodies,
shared types, and already verified `charge` and `Roots::start` signatures.
The receipt records the fresh build and the control replay. The control
matrix includes stock, flag-off, unchecked, and checked runs, a same-type
wrong-owner loan that rejects, and an unrelated original
`Execution::verify` extraction whose three generated files stay identical.

Replay the controls using a fresh build from the receipt's Aeneas commit
with the included patch applied and the pinned Charon checkout linked.

```sh
python3 verification/lean/extraction/native-deflate/project.py
python3 verification/lean/extraction/native-deflate/guard-controls.py \
  --stock "$stock_aeneas" --patched "$patched_aeneas" \
  --capture verification/lean/extraction/native-deflate/arithmetic.llbc \
  --expected verification/lean/extraction/native-deflate/Arithmetic \
  --compatibility verification/lean/extraction/execution-verify \
  --destination "$new_replay_directory"
```

`BulksketchBridge.Deflation.native_deflate_finish` links the exact source
wrapper to the full branch contract. It covers the original price and
meter result, each accepted factor and unchanged locator on rejection,
and the successful transfer to `Roots::start` with the residual degree.
The entry contract states the needed scratch and root bounds and the
backend's field multiplication law.
