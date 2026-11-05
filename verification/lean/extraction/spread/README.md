# Actual native spread extraction

This reproducer selects the original private `bulksketch::field::gf64::spread`
body from the unchanged native Cargo package. It does not introduce a Rust
wrapper, copy the arithmetic into another Rust implementation, or modify the
application body after extraction.

Run from `verification/lean` with the pinned tools already built:

```sh
python3 extraction/spread/run.py \
  --charon /absolute/path/to/pinned/charon \
  --aeneas tooling/aeneas/src/_build/default/main.exe
```

`run.py` verifies every reviewed native source hash and the Cargo/toolchain
input hashes before running Charon. It permits proof-only descendant commits:
Git HEAD is recorded, while the actual Rust content must equal the reviewed
native revision. The source branch is not edited or narrowed by hand.

The 2026-11-04 attempt completed with process exit 0 and explicit LLBC
`has_errors=false`. Aeneas produced only Types/Funs modules and no external
function/type templates. The application output is copied byte-for-byte into
`bridge/Spread`. The command records, complete LLBC, logs, generated files and
hashes are retained beside this document.

The generated body performs bounded scalar shifts/masks/OR operations and has
no iterator, allocation, externally visible mutable state, trait dictionary or custom runtime
model. The existing pinned Aeneas scalar and Result semantics are still part
of the explicit proof trust boundary. Successful extraction and elaboration
alone do not prove functional correctness or complete Rust execution coverage.

The bridge specification and independent challenges live in
`bridge/BulksketchBridge/SpreadSpec.lean` and `SpreadChallenges.lean`. They require
normal return with the exact complete 64-bit scalar for every input, plus the
universal coefficient-placement result; the proof is maintained separately.
