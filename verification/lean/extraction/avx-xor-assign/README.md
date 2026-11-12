# Stateful AVX XOR assignment

The receipt binds the original x86_64 Apple Darwin LLBC, generated Aeneas
diagnostics, and extraction tool revisions. The projector verifies the
frozen Rust file and the source spans of `xor_assign` and its three masked
memory helpers. It checks the declaration registry and full LLBC
structure, with separate validation of the decoded chunk constants and
moved call operands. The structure check binds the iterator traits, local
types, slice reborrows and metadata, Option discriminant and tuple
projections, normal loop edges, unwind cleanup and terminal Unit.

The generated plan decodes two width-eight chunk iterators, combined by
Zip, and the ordered operations in the active branch. The interpreter
evaluates both original masked load programs, the pinned register XOR
operation, and the original masked store program against the same heap.
It consumes exactly the next prefix from each view and continues until a
cursor is exhausted. The state-only outcome erases the original Unit
return.

`AvxXorLlbc.xor_assign_refines` proves the native caller's equal-length
contract under explicit word-view, write-permission and separation
premises. Every destination word is the XOR of its original word and the
corresponding original source word. The proof handles empty and short
final chunks and frames every byte outside the destination, which also
preserves the entire source view.

Run from `verification/lean`.

```sh
python3 extraction/avx-xor-assign/project.py
PYTHONDONTWRITEBYTECODE=1 python3 -O extraction/avx-xor-assign/check_controls.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.AvxXorLlbc
```

The negative controls bypass the raw digest to exercise validation of
chunk operands, load wiring, mutable destination movement, XOR and
store identity, loop edges and return. This is a scoped LLBC refinement
with modeled standard-library iterator, pointer and intrinsic semantics.
The original Aeneas output remains diagnostic. Machine provenance, Rust
aliasing, unwinding, code generation and ISA execution remain separate
obligations.
