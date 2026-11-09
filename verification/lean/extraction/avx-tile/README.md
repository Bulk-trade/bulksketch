# Original AVX tile translation

This checked capture retains the original Rust LLBC, including the first
nested mutable Zip and the later power Zip. The compiler variant returns the
two initialized arrays before computing the outer fixed point. The scoped
lowering checks the original three-callback chain and preserves every
mutable return. Both ordinary checked and strict-join replays generate the
same declarations. Source, compiler, and regression hashes are in
`receipt.json` and `controls.json`.

The Lean refinement uses the recorded masked load law, exact register
multiply and horizontal XOR, and the scoped slice and iterator models.
It proves the source's finite writeback folds and complete returned slice
behavior, including the empty odd slice error. The separate tile-row
field theorem describes the register recurrence's odd-power sum.
