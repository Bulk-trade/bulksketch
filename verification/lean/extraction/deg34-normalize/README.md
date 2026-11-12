# Original degree-three and degree-four normalization

The pinned Charon and Aeneas tools extract `deg34::normalize` and its
coefficient loop from the original Rust source. The projector retains the
three declarations verbatim and checks the shared field and kernel types.
The compiled proof uses the existing checked standard-library models.

`Normalize.normalize_refines` gives the exact output slice for either
admitted degree. The cleared input has at least six words, its Newton
denominator at index five is nonzero, and the factor scratch has room for
the monic term. Under the verified GF64 multiplication and inverse
contracts, the loop writes the lower coefficients, the wrapper writes the
supplied syndrome and monic one, and the remaining scratch stays intact.
`Normalize.normalize_field_coefficients` transports every slot through the
word-to-GF64 map. The cleared input is read through its shared slice.

A checked extraction replay reproduced all three generated files byte for
byte. The projector controls reject missing artifacts, changes to the
final coefficient or denominator slots, and changes to the frozen Rust
file. They run in standard and optimized Python modes.

```sh
python3 verification/lean/extraction/deg34-normalize/project.py
PYTHONDONTWRITEBYTECODE=1 python3 -O verification/lean/extraction/deg34-normalize/check_controls.py
cd verification/lean/bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.Normalize
```
