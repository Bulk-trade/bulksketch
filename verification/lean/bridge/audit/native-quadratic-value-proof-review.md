# Independent table linkage and original quadratic-value loop review

Approved2026-11-04; no blockers. Stable proof hashes match the owner values recorded in native-quadratic-value-proof-review.json. This review performed no builds, replay or source edits.

MapsTables proves all64row entries and all25616-by16chunk entries of the actual generated arrays equal the independent source data, retaining complete values and order. quadratic_rows_refines names the real Gf64 dictionary and returns the actual64-element source slice normally, proving its length and every value rather than relying on a successful selector premise.

MapsQuadraticValue tracks the actual runtime slice iterator over the complete static array, current remaining input word and complete independent prefix accumulator. The iterator lemma obtains the selected actual row using count<16, then derives its exact data from the full source-array linkage. No row/table correctness assumption escapes to the public endpoint.

The general u64→usize checked conversion is innerOk because masking gives0..15, and pointer_range covers both32and64bit supported usize widths. The source expect therefore takes its success path. Table indexing uses the exact nibble-bit equality and bound from the already-proved generic RawMulAccum.nibble_bounds theorem, then the actual array index operation is shown normal. Each source shift is the constant4, below64. remainingWord count16 uses the mathematical total shift to describe sixteen safe shifts; it does not execute a native shift64.

Every original body call advances one actual row, shifts the exact remaining word and adds precisely the independent chunk value. At count16 the iterator returns None before any lookup/conversion/shift. The original recursive loop completes by strict strong induction on16-count, including its terminal state; no successful loop result is assumed. The actual Gf64 endpoint initializes exactly count0/input/zero and returns the full independent16-chunk result for everyU64.

The generic non64 fallback remains in the generated body but its loop is not claimed proved by this Gf64 specialization. Independent matrix equality and normalized solver semantics are separate forthcoming composition theorems. The array/slice/runtime/frontend/compiler/ISA trusted boundary remains unchanged.
