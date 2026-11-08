# Original DegreeProbe stages

Pinned Charon extracts `bulksketch::decode::degree_probe` with transparent
application bodies on x86-64 Darwin. The checked Newton guard translator
also produces the original `DegreeProbe::run`. The projector retains 14
functions and two closure types, checks the shared declarations, and binds
the checked translator and replay to the original LLBC and source spans.

The selected standard-library bindings cover shared slice `fold`, checked
`usize` to `u8` conversion, and `sort_unstable` at the one original `OrdU64`
call site. The sort proof establishes the unique ascending permutation of
unsigned words, including duplicates, and exact write-back of the selected
prefix. Rust's documented unsigned order and ascending-permutation behavior
are the standard-library correspondence boundary. The pinned Rust smoke
control exercises counts zero through four and high unsigned values.

The original constructor, stage accessor, count conversion, and rejection
proofs give their exact value transitions. The constructor admits only
capacity and nonzero budget of at least three. Rejection clears the count
and advances a degree-three probe to degree four exactly when both bounds
permit it. The other rejection branch returns to reconstruction.

`DegreeProbeRuntime.run_refines` proves all six admitted paid phase
equations with the original generated price and exact meter transition.
The phase-specific premises cover the active stage and degree, the relevant
scratch windows, a nonzero Newton denominator at normalization, and the
candidate count for certification, verification, and canonicalization.
The equation uses the verified guard, normalization, solve, and certificate
contracts. It models the long-root verifier with the exact encoded words
and the original slice comparison, and canonicalization with the sorted
prefix and unchanged tail. The Portable specialization supplies the
encoding contract from the original default encoder and Portable insertion
selected by the backend dictionary.

The projector controls check altered generated bodies, comparator binding,
replay input, artifact manifest, and shared guard declarations.

```sh
python3 verification/lean/extraction/degree-probe/project.py
PYTHONDONTWRITEBYTECODE=1 python3 -O verification/lean/extraction/degree-probe/check_controls.py
cd verification/lean/bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.DegreeProbeRuntimeEncoding
```
