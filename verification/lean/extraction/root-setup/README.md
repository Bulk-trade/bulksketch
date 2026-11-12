# Original root traversal setup

The pinned stock Charon and checked Aeneas capture the original
`FactorWork::new`, `Roots::start` and three configuration methods without
opaque application calls. The declaration projector compares 16 retained
declarations with the raw output, verifies the embedded source and exact
LLBC bodies, and checks the reused shared declarations. Independent
checked extraction replay reproduced all three generated files byte for byte.

`RootSetup.factor_work_refines` checks all borrowed scratch regions and the
entire returned continuation. It preserves all three mutable slice splits,
the reducer table prefix, raw scratch and basis. The admitted lengths are
`3 * degree + 2` polynomial words and `degree * (degree / 2)` table words.
`RootSetup.root_start_refines` checks both the empty and copied locator
prefix, cache reset and next stage. It retains the exact native affine
preference call. The preference predictor arithmetic remains a separate
proof. `RootSetup.root_configuration_refines` checks the three setters.

Run from `verification/lean`.

```sh
python3 extraction/root-setup/project.py
python3 -O extraction/root-setup/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.RootSetup
```

The receipt records the pinned extraction and checked replay commands,
source and tool hashes, and all raw artifact fingerprints.
