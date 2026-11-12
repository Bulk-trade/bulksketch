# Native field-map semantics

Analysis date: 2026-11-04. This note describes the MapsCanonicalTrace,
MapsTraceMath and MapsQuadratic arguments. Exact proof and fixed-contract hashes
are in `bridge/audit/frozen-inputs.json`. The analysis does not include a
build or aggregate replay run.

## Canonical trace

The source loop begins at 1, carries the input as both the initial sum and
initial conjugate, and ends at 64. At source index j, the invariant tracks
traceSumPrefix j and `S^(j-1)`. Its 63 square steps therefore produce all 64
conjugates. Positive, ordered and end-64 conditions belong only to the helper
and are discharged at the universal public endpoint. Range advance returns
normally, preserves the invariant and decreases `64 - start`. The terminal
`None` at 64 ends the loop without another square.

The independent universal sum/selector theorem bounds the final sum by one.
This establishes the source `massert` and checked u64-to-u8 conversion before
simplifying `expect`. The complete trace is not truncated to obtain a successful
result. Every U64 input is covered, without a source-success, bounded-trace or
irreducibility premise.

## Full-byte trace and normalized quadratic solver

MapsTraceMath proves that the entire source selector byte is zero or one and
that its zero extension to 64 bits equals the independent traceWord. The
universal trace theorem then identifies the source result with the sum of 64
polynomial-square conjugates, preserving both normal return and the byte bound.

MapsQuadratic connects the complete 16-chunk lookup result to the independent
matrix through the universal chunk/matrix identity. On trace zero, the matrix
right-inverse identity gives `Q(Za) = a`, establishing the source square/assert
equality before `Some` is returned. On trace one, the source byte is one and the
original function returns `None` before lookup. The public contract proves
normal return for every input, correctness of returned roots, bit-0
normalization and uniqueness among normalized roots. These properties follow
from universal map theorems. No source branch or assertion is removed.

## Scope

Here absoluteTrace denotes the independently defined sum of 64 iterated
word-model polynomial squares. Its equality with Mathlib `Algebra.trace` in a
particular quotient field and the native bitword-to-polynomial quotient
representation require separate results. Exact modulus irreducibility and
universal period certificates do not establish those representations by
themselves.

At this revision, inverse wrappers and chains are unproved. Neither failed
captured-closure extraction nor successful standalone inverse extraction
establishes a native-source refinement. These contracts specialize to the real
Gf64 dictionary; generic non-64 fallback code remains present. Runtime,
frontend, compiler, ownership and ISA correspondence retain their stated trust
assumptions. The 65-statement and 14-source-body accounting and aggregate replay
are recorded separately.
