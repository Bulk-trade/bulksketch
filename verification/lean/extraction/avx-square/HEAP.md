# Accelerated square heap composition

`BulksketchBridge.AvxSquare.allocated_square_refines` joins the original
typed square body, a scalar byte-effects model for fill and seed, and the
original masked load/store LLBC for the vector phase. It returns the exact
destination and raw-scratch words, the unchanged input and table views,
and a frame for every byte outside the two mutable slices.
`allocated_block_scan` checks the complete vector trace separately, with
all bytes outside the destination unchanged.

The seed model uses the chosen layout in the pinned x86_64 Apple
capture. RawProduct has stride 16, alignment 8, and low and high words
at offsets 0 and 8. This is a capture-specific layout for the Rust-repr
type. The proof takes the corresponding byte views as premises. The
scalar trace specifies source byte effects, including destination
zeroing, the scratch low-word write, and the conditional even
destination write. The scalar trace does not model the compiler's fill
lowering or prove instruction equivalence.

Each nonempty vector load and store is connected to the original LLBC
under a witnessed allocation view. The proof checks initialization,
write permission, disjointness and non-wrapping offsets. Rust provenance
and compiler-to-ISA correspondence remain explicit obligations.

From `verification/lean`:

```sh
python3 extraction/avx-square/check_seed_layout.py
python3 -O extraction/avx-square/check_seed_layout.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.AvxSquareHeap
```
