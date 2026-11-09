# Checked affine outer-continue capture

The `checked-affine-outer-continue-v1` translator consumes the original
structured Charon capture of `affine::enumerate` at
`src/decode/affine.rs:302–347`. The pinned stock Aeneas rejects the nonlocal
continue at LLBC statement 1054. That edge is the normal exhaustion of the
inner Zip. The other two inner exits carry errors and run the outer
error epilogue.

The patch changes only `PrePasses.ml`. It requires checked mode, the exact
function name and Rust span, and the inspected LLBC edges, constructor and
cleanup sequence. A fresh boolean distinguishes normal exhaustion from error
exit. The error arms execute the original ordered iterator-storage cleanup
before the inner join. The outer index and cursor cleanup remain on the
error path after dispatch. The lowered exhaustion arm initializes a
result that the successful continuation does not read. The next observable
return always overwrites that result using an original assignment.

`control_flow.py` independently checks the original normal control flow. It
forgets the return place on statement 1054 and explores all switch arms and
reachable loop states. The check requires an original assignment at every
return. Removing the NotSplit result assignment makes it reject at statement
1188. The pinned capture and negative-control mutations are checked by
`project.py`. The borrow interpreter and its assertions are unchanged.

The receipt binds the capture, embedded Rust source, patch, pinned translator
sources, fresh compiler build, generated artifacts and control results.
The scoped translator and the standard-library bindings remain part of the
source correspondence trust boundary. The capture contains all three loops.
The active projection retains seven original declarations verbatim, with
local bindings for the mutable Enumerate backward operation, shared Zip and
checked usize shift. The active projection imports no generated external
axioms.

## Reproduction

Apply `checked-affine-outer-continue.patch` to an isolated checkout of the
pinned Aeneas source with the pinned Charon checkout linked in the usual
layout. Build the source project and run the controls from this directory.
The projector requires the original capture hash for the packaged evidence.

```sh
opam exec --root="$OPAM_ROOT" --switch=aeneas-5.3.0 -- \
  dune build --root "$VARIANT_AENEAS_SRC" -j 2
python3 guard-controls.py --stock "$STOCK_AENEAS" \
  --variant "$VARIANT_AENEAS_SRC/_build/default/main.exe" --output "$EVIDENCE"
python3 project.py
python3 -O project.py
```

The controls check the expected stock rejection, the checked translation and
unchecked rejection. They also change the function name, source span,
cleanup, error edge identity and return constructor separately. The changed
captures must hit the original nonlocal-continue rejection. The checked
variant must reproduce the stock outputs for the affine splitter and root
enumeration wrapper byte-for-byte.
