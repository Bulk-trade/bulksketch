# Dense product and native decoder checkpoint

The audit checks 50 generated-body refinements. The source ledger retains
all 344 executable native obligations from
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.

## Original Dense multiplication

The original `mul_into` body returns zero and preserves both buffers if
either input is empty. Otherwise the checked model computes
`size = a.len() + b.len()`, tests both buffers against `size`, and touches
only `size - 1` coefficients. The proof distinguishes checked scalar overflow
from the buffer assertion failures in the generated model.

The inner Zip XORs both halves of each carryless product into the exact
borrowed row. Its backward continuation applies the saved updates to the
later state. The outer enumerate loop checks each shifted window and restores
it into the full raw scratch slice. The initial raw prefix is zeroed and
the rest of the raw buffer, including the extra guard slot, is preserved.
The final loop reduces each active raw coefficient into the destination and
preserves its tail. The returned length trims exactly the trailing zeros.

Reduction sends raw XOR to GF64 addition and raw carryless multiplication to
field multiplication. At output index `k`, the field result sums exactly
the pairs with `i+j=k`. The proof identifies this with the ascending
polynomial product coefficient, including zero coefficients beyond the active
window. Normalization preserves the represented product.

The entire method and all three loops use the checked shared-loop erasure
extraction and explicit exact raw multiplication and reduction callback
equalities. The original scratch layout and source are preserved. The loop
proofs and field transport add zero duplicate body credits.

## Portable Horner

The checked context matcher now accepts the ended shared scalar loan left by
`split_last` when both scalar values and ignored child metadata match exactly.
The correction applies only to checked context matching. The regression suite
checks mismatched IDs, different child metadata, active children, nonscalar
values and unchecked mode. The original method and all four original extraction
files replay byte for byte.

The original captured callback applies Portable multiplication and XOR in a
reverse fold over the remaining coefficients. With equal lengths, the loop
writes the exact polynomial evaluation at every point. Empty coefficients
yield zeros, and unequal lengths take the original panic path. The value
model for the reverse fold and slice views remains scoped to the Rust
standard-library correspondence boundary.

## Direct two-root derivation

The original `decode::direct::two` proof covers the exact normalized pair
or `None` for nonzero `S1` with the stated GF64 callbacks. Every returned
pair has distinct nonzero roots and reproduces the given `S1` and `S3`.
The row verifier remains responsible for the other odd syndromes. The direct
body extracts with the pinned tools and its proof uses the previously
reviewed inverse wrapper.

## x86 masked-lane selection

The original `x86_vpclmul512::mask` helper was extracted for the x86 target.
For each admitted length from zero through eight, it returns exactly
`2^len - 1`. Each of its eight bits is set exactly when the lane index is
below the slice length. The proof covers the zero branch and bounds the
nonzero branch shift. The masked load and store still require address,
pointer, and instruction contracts.

## Open decoder and machine obligations

The isolated checked Berlekamp–Massey experiment propagates the common return
into the tail switch arms and clears the original early-return lowering
failure. The same original input then reaches a mandatory mutable context
match in the final coefficient-normalization loop. This experiment remains
outside the verified extraction pipeline. Reconstruction still fails at the
loop back edge. General locator fitting, root recovery, work budgets,
accelerated verification and compiler-expanded memory and ISA contracts
remain open.
