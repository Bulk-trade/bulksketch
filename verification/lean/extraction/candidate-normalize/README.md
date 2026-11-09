# Original shared candidate normalization

The checked stock capture contains the original shared candidate
normalizer, all five loops, and the original shape routing calls.
The two projections preserve the original source declarations.
The only new standard binding is the fixed unsigned tuple comparison,
checked against the pinned Rust core tuple order implementation.
Mutable slice iteration, slot swap restoration, and checked conversions
reuse existing scoped bindings. A stock replay emits identical artifacts.

The Lean endpoint proves the actual shared wrapper with the admitted
two input-sized scratch arrays and the bucket offset table. It checks
stable merge selection, the width-doubling sort, permutations, exact
mutable backward writes, adjacent nonzero compaction, and cumulative
offsets. Every admitted bucket slice then has distinct nonzero words.
