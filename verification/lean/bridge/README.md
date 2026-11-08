# Actual-source native refinement

[WorkMeter.lean](BulksketchBridge/WorkMeter.lean) proves constructor and charge
refinement against the unedited generated bodies in [Workmeter/Funs.lean](Workmeter/Funs.lean).
The charge theorem covers every generated state and U64 amount, including
overflow and exhausted states. Its projection preserves all state fields/bits;
it proves exact Rust `Ok(())`/`Err(WorkLimitExceeded)` and normal outer return.
The getter theorem proves exact observation for every state.

[Spread.lean](BulksketchBridge/Spread.lean),
[Gf64Reduce.lean](BulksketchBridge/Gf64Reduce.lean) and
[Square.lean](BulksketchBridge/Square.lean) connect the original generated
arithmetic bodies to the universal bit and polynomial-division specifications.
Reduction and square use the actual extracted source `Gf64` dictionary, without
an assumed BITS/MASK premise. Every raw 128-bit input or U64 operand is covered.
The generic conditional reduction theorem is retained; correctness of its
other-field fallback is still open.

[RawMulTable.lean](BulksketchBridge/RawMulTable.lean) and
[RawMulAccum.lean](BulksketchBridge/RawMulAccum.lean) verify both original
multiplication loops, including every reachable prefix and all subtraction,
index, cast and shift bounds. [RawMul.lean](BulksketchBridge/RawMul.lean) composes
them into exact full-128-bit raw multiplication and actual reduced multiplication.
The coefficient specification is independent of the source table/loop schedule.

[Frobenius.lean](BulksketchBridge/Frobenius.lean) additionally proves exact
normal return after the source's modulo-64 number of squarings for every input
word and U32 power. Its bounded loop retains the actual source and square call.
The new [FrobeniusPeriod.lean](BulksketchBridge/FrobeniusPeriod.lean) proves
universal word-model period 64 and upgrades the same native source item to
unmodded square iterations. The exact
[modulus theorem](BulksketchBridge/Algebra/Modulus.lean) proves irreducibility
over `Polynomial (ZMod 2)` without a prior target-field assumption.

The source [trace](BulksketchBridge/MapsTraceMath.lean),
[canonical trace](BulksketchBridge/MapsCanonicalTrace.lean),
[table](BulksketchBridge/MapsTables.lean),
[chunk loop](BulksketchBridge/MapsQuadraticValue.lean) and
[quadratic solver](BulksketchBridge/MapsQuadratic.lean) proofs establish exact
normal behavior for every input. All 320 native row/chunk entries are
kernel-linked; independent universal matrix identities supply correct roots,
trace-zero solvability and free-bit-zero uniqueness. See
[FIELD_ALGEBRA.md](../FIELD_ALGEBRA.md) for the certificate and scope details.
The [quotient-field checkpoint](../QUOTIENT_FIELD.md) proves a bijective
polynomial-basis representation, field-law transport and the actual Mathlib
`Algebra.trace`. Existing native arithmetic and both trace endpoints are
strengthened in place. The original `inverse_with_frobenius` body now computes
the represented field inverse under explicit native callback contracts, with a
closed callback instance. Its three generated declarations are retained byte
for byte and checked against the original extraction and shared dictionaries.
The subsequent [native coverage checkpoint](../NATIVE_COVERAGE.md) closes
`inverse_using`/`inverse` and Portable inverse under a named reviewed,
checks-enabled frontend variant. Seven other Portable forwarders and the original
x86-visible const square use the unchanged pinned extractor. The original
runtime and nested-loan guard remain pinned. The
[Frobenius](../FROBENIUS_TABLES.md) and [slice](../SLICE_NORMALIZATION.md)
checkpoints cover the original table generation, lookups, Portable slice
operations and Dense coefficient normalization. The
[reconciliation checkpoint](../RECONCILIATION.md) adds exact decoder dispatch
and wire-size admission, the original scalar recurrence check and Dense square, with separate GF64 locator theorems.
The [native verifier checkpoint](../NATIVE_VERIFIER.md) adds the rebuilt
verifier and its Portable seed composition, Portable insertion, default
encoding and affine linear evaluation. The [Dense product checkpoint](../DENSE_PRODUCT.md)
adds full Dense multiplication, Portable Horner, direct two-root derivation, and the x86 lane-mask helper.
The [x86 register checkpoint](../X86_REGISTER_MEMORY.md) adds the original
PCLMUL and AVX-512 register kernels and cube-root helper, plus diagnostic
proofs for the masked-memory lowering. The coverage ledger retains all
344 executable source obligations. The [stateful checkpoint](../NATIVE_STATEFUL.md)
records two separate masked-memory LLBC contracts, accelerated field maps,
feature detection and the cubic helper. The [caller checkpoint](../NATIVE_CALLER_CHAINS.md)
adds PCLMUL slice and Horner refinements, the stateful AVX XOR assignment and
difference callers, and the original degree-3/4 certificate. The
[reconstruction checkpoint](../NATIVE_RECONSTRUCTION.md) adds the original
stage wrapper, both loops, the reconstruction charge and separate LLBC
workspace admission, with a power-sum theorem for the actual stage. The
[quartic checkpoint](../NATIVE_QUARTIC.md) adds exact affine and reciprocal
quartic recovery gates and root theorems, the original batch inversion loops,
and the degree-three/four candidate output frame. The
[closed-leaf checkpoint](../NATIVE_CLOSED_LEAF.md) adds the original caller
phases, certificate acceptance, stack advance, and Newton normalization.
The [Newton guard checkpoint](../NATIVE_NEWTON_GUARD.md) adds the exact
original guard, both instances of its residual loop nest, and the
quotient-field semantics of the cleared words and recurrence. The
[BM and degree-probe checkpoint](../NATIVE_BM_DEGREE_PROBE.md) adds exact
admitted probe transitions and original BM subloop, entry and branch
refinements.

The [original BM locator checkpoint](../NATIVE_BM_LOCATOR.md) closes the
finite native recurrence and proves the monic returned locator on honest
reconstructed moments. It also adds root setup, small leaves and the
verification-stage wrapper.

The [Dense reducer checkpoint](../NATIVE_DENSE_REDUCER.md) adds the
original modular shift and table, the exact trace seed and loops, and
finite-address and allocation refinements for masked memory.

From the parent Lean directory:

```sh
python3 tooling/setup_lean_runtime.py
python3 scripts/verify_bridge.py
```

Fixed challenges and every public bridge theorem pass exact-type and
transitive-axiom checking before export/replay by Lean and independent Nanoda.
Outputs are generated under `audit/results/`.

`Workmeter` and `Arithmetic` Types/Funs are byte-identical to extraction outputs. The
concrete standard-library `Option::is_none_or` adapter is an explicit runtime
model, alongside a concrete remaining-sequence array iterator model.
[source-linkage.json](source-linkage.json)
records the native source/IR/generated-body hashes and that trust boundary.
Frontend correctness, runtime-model correspondence, Rust compilation and machine
semantics remain assumptions. [obligations.json](obligations.json) is reconciled
with the source ledger and audited challenge/theorem pairs before a successful
report. These proofs do not establish whole-library
coverage or show that every decoder path charges the meter correctly.

## Lean kernel replay and string literals

The stock Lean 4.35 replay scheduler omits the implicit `String.ofList` and
`Char.ofNat` dependencies of a string literal. Both definitions are present in
the original export, but replaying a generated panic-string proof can reach it
before those definitions. Ordinary Nanoda accepts the original export.

[ReplayExport.lean](../tooling/ReplayExport.lean) changes loading order only.
The [projection helper](../scripts/project_core_prelude.py) selects the core
literal dependency closure while preserving original export records byte for
byte. The loader checks that this prelude is an exact subset of the original
main export, then uses the unchanged parser and `Kernel.Environment.replay` from
a fresh trust-zero environment for both phases. It accepts no imported module
cache as checked proof data. Every skipped main duplicate is structurally equal
to its original prelude record submitted for checking; agreement with
kernel-regenerated constructors/recursors uses the upstream comparison rules.
The remaining main declarations and upstream quotient postchecks are mandatory.

The loader rejects unsafe/partial declarations and nonstandard axiom names.
It is compiled from frozen source by the pinned toolchain; independent Nanoda
still replays the untouched original main export. Negative fixtures exercise
malformed proofs, conflicting duplicates, extra prelude declarations and both
axiom boundaries. This is controlled-source checking of the original pinned
Lean environment and frozen challenges; canonical foundation-type pinning and
sandboxed Comparator validation remain separate integrity gates.
