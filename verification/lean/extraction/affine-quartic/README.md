# Original affine quartic extraction

The pinned checked extraction emits the complete original affine quartic
body. Its three application externals are the previously verified cubic,
quadratic and certificate functions. The projector checks the precise
reused declarations, source span, shared types and frozen extraction
artifacts. The active module retains the original function and both shared
order dictionaries verbatim, with scoped names for the two library bindings.

The pinned shared-reference `Ord::cmp` delegates to the order of its
referents. `Iterator::min` uses `reduce(Ord::min)`. The scoped runtime reads
the first element as its accumulator, then calls the existing iterator and
order methods for each remaining element. This retains the shared order's
first-on-ties behavior. The receipt fingerprints the corresponding Rust
library sources and records their line spans.

`AffineQuarticMin.kernel_minimum_refines` proves the exact native call on
the three kernel words, with three reads, two minimum selections and
normal exhaustion. `kernelMinimum_mem` proves membership in the kernel
array, and `kernelMinimum_le` bounds the selected unsigned value by each
word. The library and frontend correspondence remain explicit parts of the
bridge boundary.

Run `python3 extraction/affine-quartic/project.py` from `verification/lean`.
Build `BulksketchBridge.AffineQuarticMin` from `bridge` with the pinned Lean
toolchain. The targeted projection controls cover the emitted body, the
scoped runtime, a reused cubic declaration, raw extraction drift and a
shared type in ordinary and optimized Python.
