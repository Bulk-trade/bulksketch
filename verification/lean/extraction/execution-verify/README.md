# Original row verification stage

The pinned checked Charon and Aeneas tools extract the original
`Execution::verify` declaration. The four calls to stage charge, dispatch,
rebuilt verification, and direct probe verification bind to their separate
original declarations. The checker compares the exact types, callee
telescopes and Rust source spans. Fresh checked Aeneas replay reproduced all
three raw files byte for byte.

The outer proof keeps the original V3 dispatch, exact paid meter and both
scratch frames. The checked price models retain
the original order and every intermediate overflow of `Verify` and
`VerifyLfsr`, including for zero capacity. A pricing or meter error
precedes root-prefix reads or any scratch mutation. After a successful charge, acceptance returns
`Canonicalization` and rejection returns `VerificationFailed`. The direct
path checks both tiny-root short-circuit syndromes before encoding the full
row. The rebuilt path retains the native seed comparison, original locator
construction and exact post-comparison coefficient frame under the recorded
backend callback contracts.

The receipt records the original commands and hashes. From
`verification/lean`, run:

```sh
python3 extraction/execution-verify/project.py
python3 -O extraction/execution-verify/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.ExecutionVerifyPrice
```
