# Original AVX modular-square trait selector

Stock checked Aeneas retains the exact `Vpclmul512::square_mod` method at
`src/backend/x86_vpclmul512.rs:106–114`. Per-sibling opacity scopes the
other trait methods. The selected method remains structured. Its free
square callee is bound to the already checked original projection. A
fresh replay reproduced all three original generated files byte for byte.

`square_mod_entry_refines` proves exact decline and frame preservation
when the field width differs from 64, and the true branch of the
original free kernel. `AvxSquare.square_mod_remainder` connects
every active output word to the monic remainder and preserves both
slice lengths. `backend_law_of_original_selector` supplies the Dense
accelerated backend law when this exact GF64 selector is installed.
It uses explicit masked slice laws, with the individual masked access
views proved from the original allocation-scoped LLBC contracts.
Hardware execution, Rust provenance and compiler correspondence remain
separate from these slice results.

Run from `verification/lean`.

```sh
python3 extraction/avx-square-entry/project.py
python3 -O extraction/avx-square-entry/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.AvxSquareEntry
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake env lean ../extraction/avx-square-entry/Axioms.lean
```
