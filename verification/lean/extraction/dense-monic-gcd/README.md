# Original Dense monic GCD

The stock checked Aeneas capture retains the original
`Dense::monic_gcd_into` body and both loop declarations verbatim.
The original division call is an explicit argument with the same typed
slot as the exact-division projection. It is constrained by the stated
normalization, frame, descent and polynomial-decomposition laws.

The two original `core::mem::swap` calls operate on the lent references
held in the local mutable slots. The scoped Lean binding returns the
forward swap and the exact inverse permutation of the later slot
values. In pinned rust-src, `core/src/mem/mod.rs:830` implements
`swap` with `typed_swap_nonoverlapping` on its disjoint mutable slots.

The finite refinement follows the exact four-part scratch split,
both input copies, the two swaps per Euclidean iteration, returned
quotient, remainder and raw frames, and the final zeroed, copied or
inverse-scaled destination prefix. The algebra endpoint shows that
the returned active coefficients are Mathlib's canonical monic GCD
in the exact GF64 field under the div/rem polynomial identity.

A second stock checked translation reproduced all three generated
files byte for byte. The receipt and checker pin capture roots, tool
fingerprints, checked flags, source spans and replay artifacts.

Run from `verification/lean`.

```sh
python3 extraction/dense-monic-gcd/project.py
python3 -O extraction/dense-monic-gcd/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.DenseGcdAlgebra
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake env lean ../extraction/dense-monic-gcd/Axioms.lean
```
