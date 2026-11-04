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
