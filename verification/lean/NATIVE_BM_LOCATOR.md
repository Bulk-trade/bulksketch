# Original Berlekamp–Massey locator and recovery stages

The ledger retains 344 native executable obligations. The associated record
contains 111 original Aeneas body refinements, including the nine refinements
described here, under the stated source, translator, runtime and kernel contracts. The five scoped LLBC
contracts remain separate. Production Rust is unchanged.

## Berlekamp–Massey

The original locator refines the finite recurrence from entry to return.
The proof derives all iteration bounds from the admitted syndrome and
scratch sizes, the degree budget and the shift window invariant. It covers
every work charge, exact early result and meter, all three mutable rows
and the final normalization and reversal. The recursion consumes exactly
one index on each continuation. The extracted source remains the checked
25-declaration projection with both typed mutable writebacks preserved.

On an admitted reconstructed row, the original loop carries a zero
residual prefix, a nonzero connection constant and scale, and an anchor
for the previous row. The odd-index skip follows from characteristic
two and the reconstructed square relation. A growth step copies the
old connection into the previous row and installs the current
discrepancy and power as its new anchor.

For the positive moments of an admitted distinct nonzero support,
the native locator either returns an exact pricing or meter error
or returns the support's degree and its monic locator. A finite
geometric-series reference bounds every growth by the support size.
The terminal recurrence and Vandermonde uniqueness give the exact
degree and polynomial. The original split-back functions put that
polynomial in the first returned scratch row, with the other live rows
and original suffix in source order.

## Root traversal and verification

The original FactorWork partition, three root setters, root start, and
degree-zero through degree-two leaf have source refinements. The root
start retains the original affine preference call. The small leaf
covers exact solver inputs and outputs under the GF64 callback laws,
rejects zero roots, and proves the bounded append and state count
before the original pending-frame advance.

The original probe verification and Execution verification stage
have exact refinements. The stage proof composes the native dispatch,
admitted verifier branches, independent checked prices in source
operation order, early errors, exact meter and scratch frames, and
canonicalization-stage return.

The [root traversal](NATIVE_ROOT_RUN.md) documentation describes the conditional
factor, candidate and deflation contracts. The [Portable theorem](README.md)
composes the ordinary no-hint decoder route, including its admitted work bound.
Public caller admission, shared-job accounting, hint and V3 composition,
accelerated end-to-end execution, physical memory and compiler-expanded ISA
correspondence remain outside these component proofs.

Run the aggregate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
