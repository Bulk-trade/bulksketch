# Original Dense reducer, trace loops and finite memory

All 344 native executable obligations remain in scope. The ledger records
113 original Aeneas body refinements under the recorded contracts, and
five separate stateful LLBC contracts. Production Rust is unchanged.

## Dense modular square table

The original `times_x_mod` checks its overlapping prefix move, zero
constant, low modulus prefix and scale-XOR call. The scoped RangeTo
library binding reads the original prefix before writing the overlap.
For an admitted monic modulus, the returned row has the original width
and represents multiplication by (X) in the quotient ring.

The original `prepare_square_table` checks the exact table and work
frames. Its first row represents (X^d) for even degree (d) and
(X^{d+1}) for odd degree. Successive rows advance by two powers. The
native loop proof retains the final work row and the original table
suffix. The quotient proof derives each row from the original shifts.

With that table invariant, the scalar square's low monomials and high
table contributions give the exact monic remainder of the square.
This is the polynomial specification for the pending whole native
`square_mod_into` proof.

The checked table translator accepts only the scoped identical
marker-free shared Option payload and empty ignored projector. The
stock symbol, region, loan and mutable writeback mapping is retained.
Checked replay reproduces all three artifacts. Stock, disabled and
unchecked controls fail at the original join. Unrelated Portable XOR
artifacts match the stock translator.

## Trace splitting

The original trace seed closure and basis extension return the exact
seed normalization, basis words, final length and untouched frames.
The original Frobenius loop proof checks its exact scratch recurrence
and evaluates it at factor roots under the explicit modular-square
contract. The 64-step pointwise result is Mathlib `Algebra.trace` in
the exact GF64 quotient. The full trace stage and general traversal
remain separate obligations.

## Finite address and allocation contracts

The original masked load, store, XOR assignment and difference LLBC
have finite 64-bit address refinements. Under the explicit Rust slice
premises, every active byte stays within the same supplied live
allocation, has a canonical effective address, and satisfies the
signed pointer-offset bound. The contracts check the exact bytes,
the difference flag and the frame outside the destination. These
strengthen existing LLBC endpoints. Rust provenance, execution of the
instructions, and compiler correspondence remain open.

Run the aggregate from `verification/lean`.

```sh
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 python3 scripts/verify_all.py
```
