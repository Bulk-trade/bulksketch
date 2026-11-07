# Mutable slice traversal and dense normalization

The scoped mutable Zip model pairs a mutable slice iterator with a shared
slice iterator. Each cursor advances only when both sides have a remaining
element. The backward continuation updates the yielded left position on the
later state, preserving writes from later steps and the shared right iterator.
The model and proofs cover both cursor bounds, exhaustion, failure propagation
and the retained frame.

The original Portable XOR, square and scale-XOR bodies use the same checked
traversal theorem. Equal lengths produce a complete destination frame.
Unequal lengths take the original panic path before construction. Scale zero
preserves the destination, scale one calls the proved original XOR method,
and other scales use the proved GF64 multiplication body.

The shared-slice reverse position model visits the remaining suffix from the
end, threads the original predicate state, and retains the unvisited prefix.
The map-or binding selects the default for None and invokes the original
callback for Some. The original `normalized_len` proof checks the returned
position and its increment, and yields the length after removing trailing zeros.

The original `Dense::xor_coefficient` proof checks both assertions, bounded
growth and the full output buffer. Newly active slots are cleared before the
selected coefficient is XORed, and the inactive tail is preserved. On the
active prefix, the exact GF64 quotient polynomial changes by addition of the
selected monomial. Removing the trailing zero suffix preserves that polynomial.

The ledger records 37 source-body refinements and 344 retained executable
obligations. The model laws and polynomial transport add no source-body count.
The frozen audit includes 113 endpoints. Original source declarations and
reused dependencies are checked by the four new extraction projectors.

The runtime bindings describe the supported Rust standard-library value
operations. Standard-library and extractor correspondence, physical aliasing,
pointer provenance, drop behavior and ISA semantics retain their recorded
trust assumptions. Remaining targets include the Dense square and multiplication
kernels, Horner evaluation, decoder completeness, and machine memory and ISA
contracts.
