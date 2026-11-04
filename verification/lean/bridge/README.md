# Actual-source WorkMeter refinement

[WorkMeter.lean](BulksketchBridge/WorkMeter.lean) proves constructor and charge
refinement against the unedited generated bodies in [Workmeter/Funs.lean](Workmeter/Funs.lean).
The charge theorem covers every generated state and U64 amount, including
overflow and exhausted states. Its projection preserves all state fields/bits;
it proves exact Rust `Ok(())`/`Err(WorkLimitExceeded)` and normal outer return.

From the parent Lean directory:

```sh
python3 tooling/setup_lean_runtime.py
python3 scripts/verify_bridge.py
```

Three fixed challenges and every public bridge theorem pass exact-type and
transitive-axiom checking before export/replay by Lean and independent Nanoda.
Outputs are generated under `audit/results/`.

`Types.lean` and `Funs.lean` are byte-identical to the extraction outputs. The
concrete standard-library `Option::is_none_or` adapter is an explicit runtime
model, not an application axiom. [source-linkage.json](source-linkage.json)
records the native source/IR/generated-body hashes and that trust boundary.
Frontend correctness, runtime-model correspondence, Rust compilation and machine
semantics remain assumptions; the two proofs do not establish whole-library
coverage or show that every decoder path charges the meter correctly.
