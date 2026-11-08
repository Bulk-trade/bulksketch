# Original root trace loops

The pinned stock translator captures the original `Roots::trace` closure,
basis-extension loop, Frobenius loop and wrapper. Checked replay reproduced all
three original generated files byte for byte. The projector checks eight
verbatim declarations, the original LLBC spans, unchanged source, the target,
the tool hashes and the shared types.

The projection binds `Option::get_or_insert_with` only at the original
trace call. Pinned Rust core `library/core/src/option.rs:1807` calls the
initializer only on the absent branch and returns a mutable borrow of the
present entry. Its value-level model retains both the Option writeback and
the closure's captured mutable length. The stock external template omits
that closure state in its function type, although the stock caller uses it.
The runtime notation preserves all eight generated declaration bodies.

`seed_closure_refines` proves the exact initialized array and live length.
`basis_extension_refines` checks the whole original basis loop through the
requested direction, including cache reuse, the exact recurrence, and both
untouched prefixes and suffixes.

`trace_loop_refines` checks the original 63-advance range, every normalized
slice copy and XOR update, and the scratch lengths. At each root of the
factor it returns the 64-term trace, which `trace_at_is_algebra_trace`
identifies with Mathlib's algebra trace. This theorem has an explicit
`ModularSquareLaw` premise on the original Dense square application slot.
The typed argument introduces no axiom. The original Dense implementation
still needs to discharge that law. This package gives no whole-wrapper
credit for `Roots::trace`.

Run from `verification/lean`:

```sh
python3 extraction/root-trace/project.py
python3 -O extraction/root-trace/project.py
cd bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.RootTraceField
```
