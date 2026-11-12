# Table linkage and original quadratic-value loop analysis

Analysis date: 2026-11-04. Proof fingerprints are recorded in
`bridge/audit/frozen-inputs.json`. This note describes the source
argument; it does not include a build or replay run.

MapsTables proves that all 64 row entries and all 256 entries of the 16-by-16
chunk table in the generated arrays equal the independently specified data,
with their complete values and order preserved. `quadratic_rows_refines` names
the real Gf64 dictionary and proves normal return of the actual 64-element
source slice, including its length and every value.

MapsQuadraticValue tracks the runtime slice iterator over the complete static
array, the remaining input word and the independent prefix accumulator. The
iterator lemma obtains the actual row when `count < 16`; full source-array
linkage identifies its exact data. The public contract has no row or table
correctness premise.

Masking bounds the u64-to-usize conversion input by 15, so the checked conversion
returns Rust `Ok`. The pointer_range result covers both supported usize widths,
32 and 64 bits. The source `expect` therefore follows its success branch. Table
indexing uses the nibble-bit identity and bound from
`RawMulAccum.nibble_bounds`, followed by normal execution of the actual array
index operation. Each native shift is the constant 4, below 64. The mathematical
total shift in remainingWord at count 16 describes sixteen safe shifts; the
source never executes a shift by 64.

Every source body call advances one actual row, shifts the exact remaining word
and adds the independently specified chunk value. At count 16 the iterator
returns `None` before lookup, conversion or shift. Strong induction on
`16 - count` proves the recursive loop, including its terminal state, without
assuming a successful loop result. The Gf64 endpoint initializes count 0, the
input word and a zero accumulator, then returns the complete 16-chunk result for
every U64 input.

The generic non-64 fallback remains in the generated body; this Gf64 contract
does not prove that loop. Universal matrix equality and normalized solver
semantics require separate composition theorems. Array, slice, runtime,
frontend, compiler and ISA correspondence retain their stated trust assumptions.
