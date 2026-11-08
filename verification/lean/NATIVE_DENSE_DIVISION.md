# Original Dense division wrappers and accelerated square

The ledger retains all 344 native executable obligations. This checkpoint
adds the original Dense exact-division and monic-GCD bodies and the
original AVX-512 free square kernel under their recorded contracts.
Production Rust is unchanged.

The original exact-division wrapper preserves the quotient on zero
remainder. On nonzero remainder it clears exactly the original admitted
quotient prefix and retains the returned remainder and raw scratch.
The native GCD wrapper rotates the three borrowed work slots in the
original order, uses a decreasing normalized remainder length, and
returns Mathlib's canonical monic GCD in its destination prefix.
Both wrapper projections pass an explicit original div/rem callee slot.

The descending div/rem model handles the zero-factor skip, unit XOR and
general carryless product paths. Its residual polynomial uses only the
live raw prefix, because the original code retains eliminated top
words in memory. Its normalized quotient and remainder satisfy the
dividend decomposition and strict remainder degree. The model supplies
the Euclidean division laws once the original body equation is linked.
The full native div/rem correspondence remains open at the current
extraction and induction boundary.

The original AVX-512 free modular-square kernel checks the seed loop,
high row fold, and eight-word block scan including the final short
block. The result preserves raw scratch widths and high words, writes
the exact coefficient squares in the admitted low words, and checks
the exact destination under the stated masked load and store laws.
The accelerated trait selector and field remainder linkage have
separate proof obligations. Rust pointer provenance, hardware ISA
execution and full compiler correspondence remain open.

Run the aggregate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
