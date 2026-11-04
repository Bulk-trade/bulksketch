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
The period-64 field identity is a separate open algebraic obligation.

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
