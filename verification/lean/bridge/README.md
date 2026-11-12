# Native-source refinement proofs

The bridge relates the pinned Rust implementation to algebraic specifications
through its Charon/Aeneas translations. The coverage ledger retains all 344
executable native source obligations. Each refinement has an explicit source,
translator, runtime and memory contract; a checked component does not imply
whole-library correctness.

## Scalar arithmetic and field representation

[Spread.lean](BulksketchBridge/Spread.lean),
[Gf64Reduce.lean](BulksketchBridge/Gf64Reduce.lean) and
[Square.lean](BulksketchBridge/Square.lean) connect the original generated
arithmetic bodies to the universal bit and polynomial-division specifications.
Reduction and square use the actual extracted `Gf64` dictionary, without an
assumed BITS/MASK premise. Every raw 128-bit input or U64 operand is covered.
The generic conditional reduction theorem is retained; its other-field fallback
is outside the proved specialization.

[RawMulTable.lean](BulksketchBridge/RawMulTable.lean) and
[RawMulAccum.lean](BulksketchBridge/RawMulAccum.lean) verify both original
multiplication loops, including every reachable prefix and all subtraction,
index, cast and shift bounds. [RawMul.lean](BulksketchBridge/RawMul.lean) composes
them into exact full-128-bit raw multiplication and reduced multiplication.
The coefficient specification is independent of the source table and loop
schedule.

[Frobenius.lean](BulksketchBridge/Frobenius.lean) proves exact normal return after
the source's modulo-64 number of squarings for every word and U32 power.
[FrobeniusPeriod.lean](BulksketchBridge/FrobeniusPeriod.lean) proves word-model
period 64 and identifies the result with unmodded square iterations. The exact
[modulus theorem](BulksketchBridge/Algebra/Modulus.lean) proves irreducibility
over `Polynomial (ZMod 2)` without assuming the target field laws.

The source [trace](BulksketchBridge/MapsTraceMath.lean),
[canonical trace](BulksketchBridge/MapsCanonicalTrace.lean),
[table](BulksketchBridge/MapsTables.lean),
[chunk loop](BulksketchBridge/MapsQuadraticValue.lean) and
[quadratic solver](BulksketchBridge/MapsQuadratic.lean) proofs establish exact
normal behavior for every input. All 320 native row/chunk entries are
kernel-linked. Universal matrix identities establish correct roots,
trace-zero solvability and uniqueness with free bit zero. The
[field-algebra documentation](../FIELD_ALGEBRA.md) gives the certificates and
scope.

The [quotient-field proofs](../QUOTIENT_FIELD.md) establish a bijective
polynomial-basis representation, field-law transport and Mathlib's
`Algebra.trace`. The original `inverse_with_frobenius` computes the represented
field inverse under explicit native callback contracts, with a closed callback
instance. Its three generated declarations are retained byte for byte and
checked against the extraction and shared dictionaries.
[Enclosing-inversion proofs](../NATIVE_COVERAGE.md) cover `inverse_using`,
`inverse` and Portable inverse through a pinned, checks-enabled frontend
variant. Seven other Portable forwarders and the original x86-visible const
square use the unchanged pinned extractor. The runtime and nested-loan guard
remain pinned. [Frobenius-table proofs](../FROBENIUS_TABLES.md) cover the original
generators and lookups, and [slice proofs](../SLICE_NORMALIZATION.md) cover
Portable slice operations and Dense coefficient normalization.

## Polynomial kernels and decoder stages

The component contracts retain original function bodies, state transitions,
workspace frames and work-meter effects. Their assumptions and exact source
relationships are documented by subject.

| Subject | Checked behavior |
| --- | --- |
| [Dispatch and reconciliation](../RECONCILIATION.md) | Decoder dispatch, wire-size admission, scalar recurrence matching and Dense square, with separate GF64 locator theorems |
| [Rebuilt verification](../NATIVE_VERIFIER.md) | Original rebuilt verifier, Portable seed composition, insertion, default encoding and affine linear evaluation |
| [Dense product and evaluation](../DENSE_PRODUCT.md) | Full Dense multiplication, Portable Horner, direct two-root derivation and the x86 lane-mask helper |
| [Reconstruction](../NATIVE_RECONSTRUCTION.md) | Original wrapper and both loops, reconstruction pricing, a separate LLBC workspace-admission contract, and stage power sums |
| [Quartic recovery](../NATIVE_QUARTIC.md) | Affine and reciprocal quartic gates and root theorems, batch inversion loops and the degree-three/four candidate output frame |
| [Closed leaves](../NATIVE_CLOSED_LEAF.md) | Original caller phases, certificate acceptance, stack advance and Newton normalization |
| [Newton guards](../NATIVE_NEWTON_GUARD.md) | Original guard, both residual loop nests, quotient-field clearing and recurrence semantics |
| [Degree probe and BM loops](../NATIVE_BM_DEGREE_PROBE.md) | Admitted probe transitions and original BM subloop, entry and branch refinements |
| [BM locator](../NATIVE_BM_LOCATOR.md) | Finite native recurrence, monic locator on honest reconstructed moments, root setup, small leaves and verification-stage wrapper |
| [Dense reducer](../NATIVE_DENSE_REDUCER.md) | Original modular shift, table and square, exact trace stage and finite-address/allocation memory refinements |
| [Dense division](../NATIVE_DENSE_DIVISION.md) | Exact-division and GCD wrappers, algebraic division model and original AVX-512 square kernel |
| [Root traversal](../NATIVE_ROOT_RUN.md) | Original root dispatcher, factor division, affine offset, splitter and AVX square heap effects |

The [end-to-end Portable theorem](BulksketchBridge/PortableSketchEndToEnd.lean)
composes the ordinary no-hint GF64 route for valid equal-shape in-memory
sketches. It returns distinct IDs representing their exact symmetric difference,
including zero. Its input, capacity, per-row scratch and work assumptions are
stated in the [verification guide](../README.md).

## Accelerated arithmetic and memory

The [x86 register proofs](../X86_REGISTER_MEMORY.md) cover original PCLMUL and
AVX-512 register kernels and cube-root arithmetic, with diagnostic proofs for
masked-memory lowering. The [stateful LLBC contracts](../NATIVE_STATEFUL.md)
separately cover the two masked-memory operations, accelerated field maps,
feature detection and the cubic helper.

The [native caller proofs](../NATIVE_CALLER_CHAINS.md) cover PCLMUL slice and
Horner methods, stateful AVX XOR assignment and difference callers, and the
original degree-three/four certificate. These component contracts retain their
explicit memory and ISA assumptions; they do not establish accelerated
end-to-end decoder correctness or physical pointer provenance.

## Work accounting

[WorkMeter.lean](BulksketchBridge/WorkMeter.lean) proves constructor, charge and
getter refinement against the unedited generated bodies in
[Workmeter/Funs.lean](Workmeter/Funs.lean). The charge theorem covers every
generated state and U64 amount, including overflow and exhausted states. It
preserves all state fields and bits, establishes exact Rust `Ok(())` or
`Err(WorkLimitExceeded)` and normal outer return, and proves exact getter
observation for every state.

## Checking and trust boundary

From the containing Lean directory:

```sh
python3 tooling/setup_lean_runtime.py
python3 scripts/verify_bridge.py
```

Fixed challenges and every public bridge theorem undergo exact-type and
transitive-axiom checking before export and replay by Lean and independent
Nanoda. Outputs are generated under `audit/results/`.

`Workmeter` and `Arithmetic` Types/Funs are byte-identical to extraction outputs.
The standard-library `Option::is_none_or` adapter is an explicit runtime model,
alongside the remaining-sequence array iterator model.
[source-linkage.json](source-linkage.json) records native source, IR and
generated-body hashes and the trust boundary. Frontend correctness,
runtime-model correspondence, Rust compilation and machine semantics remain
assumptions. [obligations.json](obligations.json) is reconciled with the source
ledger and audited challenge/theorem pairs before a successful report. These
proofs do not establish whole-library coverage or correct metering of every
decoder route.

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
