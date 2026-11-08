# Original small-factor recovery leaf

The original `Roots::leaf` body extracts with the stock checked translator.
The two scoped opaque application calls resolve to the existing verified
`roots::charge` and `Roots::advance` declarations. Checked replay reproduced
all three generated files byte for byte. The exact projector compares the
embedded source, shared types and application binding hashes.

`RootLeaf.root_leaf_refines` covers degrees zero, one and two under the
admitted slice bounds and GF64 arithmetic contract. It preserves charge
failure and the final meter, including the degree-two zero-linear and
unsolved-quadratic exits. The successful candidate path checks the exact
normalized quadratic input, zero-root rejection, bounded destination write
and count increment before the verified advance.

```sh
python3 extraction/root-leaf/project.py
python3 -O extraction/root-leaf/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.RootLeaf
```

The remaining traversal stages and their completeness proofs are separate.
