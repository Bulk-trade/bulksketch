# Checked affine multiple Zip endings

The `checked-affine-multiple-zip-ends-v1` variant translates the original
structured `affine::multiple` body from `src/decode/affine.rs:100–170`.
The original Dense modular square is the only opaque application callee in
this capture. The active Lean projection binds that call explicitly and
retains nine source declarations verbatim.

Stock Aeneas tries to destructure a nested backward-loan history when the
outer column loop reaches its fixed-point join. The patch scopes the repair
to checked mode, an opt-in flag, and the exact original row and witness Zip
storage-death sites. It resolves the terminal symbolic value from the actual
iterator or its mutable borrower and verifies the matching left and right
loop abstractions before ending them. Each owns a distinct singleton
region. The original drop, abstraction ending, and writeback operations
remain in use.

At the scoped endings the typed mutable and shared Zip regions have disjoint
ownership, so the substitution visitor updates the owned projector. At the
outer join the continuation merge can encounter an ended Zip projector
whose sole consumed child is empty. The guarded merge preserves the
expression, its metadata, and its marker. A mutable-region rename on the
right arm and its subsequent unmarked replay retain the same shared
sibling. Other shapes still follow the original checks.

The projector pins the original Charon bytes, the four embedded Rust
sources, the translator patch, the five modified translator source files,
the clean compiler binary and all three emitted Lean files. Stock Charon
recapture matches the original after normalizing the destination field.
The scoped translator and Rust runtime correspondence remain part of the
source trust boundary.

The operational theorem is `BulksketchBridge.AffineMultiple.native_multiple_refines`.
It verifies the wrapper, pivot search, both normalization loops, and the
finite column trace with the original Dense square bound to the call.
The trace includes the exhausted-iterator panic. Proving that this panic
is unreachable and that the returned polynomial is minimal requires the
separate affine-elimination invariant.

## Reproduction

Apply `checked-affine-multiple-zip-ends.patch` to the pinned clean Aeneas
checkout and link the pinned Charon source in the usual layout. Build the
isolated compiler and run the controls from this directory.

```sh
opam exec --root="$OPAM_ROOT" --switch=aeneas-5.3.0 -- \
  dune build --root "$VARIANT_AENEAS_SRC" -j 2
python3 guard-controls.py --stock "$STOCK_AENEAS" \
  --variant "$VARIANT_AENEAS_SRC/_build/default/main.exe" --output "$EVIDENCE"
python3 project.py
python3 -O project.py
```

Stock, flag-off, unchecked, and the changed-lifetime capture reject at the
original outer-loop borrow guard. The checked variant replays byte-for-byte.
The affine-splitter compatibility capture retains its stock artifacts.
