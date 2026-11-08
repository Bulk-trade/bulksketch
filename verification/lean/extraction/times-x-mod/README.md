# Original Dense modular shift

The stock checked extraction retains the original `times_x_mod` body,
its RangeTo dictionary and two source types. The scoped `copy_within`
binding takes a snapshot of the original source prefix and then writes
it at the destination. This models the original overlapping
`ptr::copy` in pinned rust-src `core/src/slice/mod.rs` at line 4376.
The compiled source projection and all three generated files match the
checked stock replay.

`TimesXMod.times_x_mod_refines` checks the exact original slice
operations and arithmetic call. `TimesXMod.times_x_mod_polynomial`
proves the fixed-width residue equation under monicity and the exact
GF64 scale-XOR contract.

Run the projector from `verification/lean`.

```sh
python3 extraction/times-x-mod/project.py
python3 -O extraction/times-x-mod/project.py
```
