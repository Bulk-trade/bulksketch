# Original AVX-512 modular-square kernel

Stock checked Aeneas retains the original free function at
`src/backend/x86_vpclmul512.rs:218–250` and all six emitted loop declarations.
The capture explicitly scopes the original masked `load` and `store` as
application slots. The projection reuses the existing checked register
operations, scalar PCLMUL square, native byte-order and ceiling-division
bindings. The local Skip model consumes the delayed prefix using the
read-only enumeration's exact cursor transitions. The replay reproduced
all three generated files byte for byte.

`BulksketchBridge.AvxSquare.square_mod_refines` checks the original low
seed and scratch writes, both high-row accumulation registers, exact
block traversal and returned short-tail writeback. `squareResult`
retains the complete output and raw scratch, including untouched high
raw words and the input-independent scratch suffix. The theorem uses
explicit slice views for masked memory. The existing LLBC address and
allocation contracts describe the conditions under which those views
are sound. Physical execution, compiler correspondence and the trait
wrapper remain separate.

Run from `verification/lean`.

```sh
python3 extraction/avx-square/project.py
python3 -O extraction/avx-square/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.AvxSquare
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake env lean ../extraction/avx-square/Axioms.lean
```
