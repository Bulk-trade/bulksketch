# Original Dense division and accelerated square

The ledger retains all 344 native executable obligations. This checkpoint
checks the original Dense div/rem, exact-division and monic-GCD bodies and the
original AVX-512 free square kernel and trait selector under their recorded contracts.
Production Rust is unchanged.

The original, unoutlined `Dense::div_rem_into` now checks against the
word model. The proof covers initialization, every descending quotient
offset, zero, unit and general factors in both inverse branches, final
prefix reduction, normalized lengths and the full scratch frame. The
generated-model failure theorems cover an empty divisor, rejected inverse,
checked size overflow and insufficient scratch after a successful inverse.
The exact body discharges both Euclidean GCD division premises and binds
the original root factor-division proof to the native div/rem call.

The frozen `checked-dense-div-rem-v1` translator enables this extraction
with mandatory invariant checks on the exact Charon capture. Its scoped
guards distinguish the two Zip regions, confirm the raw slice and
iterator loan chain before stock cleanup, and match the exhausted Zip
by symbolic identity. A fresh pinned-tool build reproduced all three
generated files byte for byte. The receipt retains wrong-owner,
region-alias and wrong-terminal controls, plus stock, flag-off,
unchecked and unrelated Portable XOR controls. The scoped translator
and Rust runtime correspondence are explicit trust boundaries.

The original exact-division wrapper preserves the quotient on zero
remainder. On nonzero remainder it clears exactly the original admitted
quotient prefix and retains the returned remainder and raw scratch.
The native GCD wrapper rotates the three borrowed work slots in the
original order, uses a decreasing normalized remainder length, and
returns Mathlib's canonical monic GCD in its destination prefix.
The returned size is zero exactly for zero GCD, and otherwise equals
the canonical GCD degree plus one. Both generic wrapper projections
retain a typed div/rem slot that can be instantiated with the proved body.

The descending div/rem model handles the zero-factor skip, unit XOR and
general carryless product paths. Its residual polynomial uses only the
live raw prefix, because the original code retains eliminated top
words in memory. Its normalized quotient and remainder satisfy the
dividend decomposition and strict remainder degree. The model supplies
the Euclidean division laws through the proved body equation.

The original AVX-512 free modular-square kernel checks the seed loop,
high row fold, and eight-word block scan including the final short
block. The result preserves raw scratch widths and high words, writes
the exact coefficient squares in the admitted low words, and checks
the exact destination under the stated masked load and store laws.
The original trait selector declines non-64-bit fields with both
slices preserved and otherwise invokes the proved kernel. Its GF64
result is the exact monic remainder. Installing that typed selector
with the masked memory laws discharges Dense's accelerated remainder
and frame premise. The individual allocation-scoped load and store
results are tied to the existing original LLBC contracts. Rust pointer
provenance, hardware ISA execution and full compiler correspondence
remain open.

Run the aggregate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
