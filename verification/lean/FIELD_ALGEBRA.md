# Field algebra and native maps checkpoint

This records the earlier field-algebra checkpoint. The subsequent
[quotient-field checkpoint](QUOTIENT_FIELD.md) closes the word representation
and algebra-trace transport listed as remaining below, and verifies the original
`inverse_with_frobenius` body. The enclosing inversion wrappers remain open.

This checkpoint preserves native revision
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. Rust implementation and build inputs
are unchanged. All earlier frozen statements and generated function definitions
remain present.

## Exact modulus irreducibility

[ModulusSpec.lean](bridge/BulksketchBridge/Algebra/ModulusSpec.lean) defines
`P = X^64 + X^4 + X^3 + X + 1 : Polynomial (ZMod 2)`.
[Modulus.lean](bridge/BulksketchBridge/Algebra/Modulus.lean) proves genuine
`Irreducible P`, with the independent challenge spelling out that literal
polynomial. No field instance for the target quotient is assumed.

The proof checks 64 adjacent modular-square polynomial identities. They give
`X^(2^64) = X mod P`. It also checks an explicit Bézout identity between `P` and
the degree-32 Frobenius remainder plus `X`, proving their coprimality. Monicity
and degree 64 are proved. An irreducible factor of `P` must then have degree
dividing 64; a degree below 64 would divide 32 and contradict the Bézout result.
Thus the factor has full degree and the target polynomial is irreducible.

The remainder after 32 squarings is represented by coefficient word
`0x5c62236777028505`. The displayed identities, not that numeric result alone,
are the proof evidence. A checked opaque subtype packages the explicit function
`n => X^(2^n)` and its equality proof. This prevents accidental expansion of an
enormous polynomial power during definitional equality. Its body is exported
and kernel-checked; it is not an axiom or an irreducibility assumption.

The exact polynomial theorem passed stock Leanchecker and independent Nanoda
on the same untouched export. It grants no additional Rust-function credit.

## Universal word-model period

[PeriodSpec.lean](BulksketchProofs/Field/PeriodSpec.lean) adds a pure square-word
model definitionally matching the earlier frozen Frobenius model. It changes
none of those earlier meanings.

[Period.lean](BulksketchProofs/Field/Period.lean) proves XOR linearity and that
two zero/XOR-preserving maps agreeing on all 64 polynomial-basis words agree on
every word. [PeriodBasis.lean](BulksketchProofs/Field/PeriodBasis.lean) supplies
the complete kernel-checked basis certificate for 64 squarings. Hence

`iterateSquare 64 input = input`

for every 64-bit input, and `iterateSquare (n % 64) input = iterateSquare n input`
for every natural `n`. This enumerates 64 basis indices, not all operand words.
The proof is independent of the irreducibility theorem.

[FrobeniusPeriod.lean](bridge/BulksketchBridge/FrobeniusPeriod.lean) proves exact
correspondence to the old frozen model and strengthens the existing actual
native Frobenius refinement to unmodded `power.val` iterations. It remains one
native source item, with both old and stronger contracts retained.

## Trace and complete table identities

[FieldTables.lean](BulksketchProofs/Generated/FieldTables.lean) contains the 64
native quadratic rows, all 256 chunk entries, and 64 generated transpose
columns. Literal extraction is strict and source-pinned. The transpose is
untrusted certificate data until the 4,096 row/column bit equalities are checked.
[MapsTables.lean](bridge/BulksketchBridge/MapsTables.lean) independently links
all 320 original row/chunk literals to the actual generated Rust constants.

[Maps.lean](BulksketchProofs/Field/Maps.lean) and its certificate module prove
universal identities using complete finite certificates and linearity. Let
`S` be the square-word map, `T` the XOR sum of all 64 conjugates, `Z` the
independent row-matrix map and `Q(z) = S(z) XOR z`.

| Identity | Meaning |
| --- | --- |
| `T(a) = bit61(a) XOR bit63(a)` as a complete zero/one word | Exact independent conjugate-sum trace selector |
| Horner trace equals the direct conjugate sum | Efficient certificate evaluation preserves the intended sum |
| Every chunk entry equals its matrix contribution | All 16-by-16 entries checked |
| Complete chunk lookup equals `Z(a)` | Every input word, not a table sample |
| `Q(Z(a)) = a XOR (traceBit(a) ? bit63 : 0)` | Right inverse on trace-zero inputs |
| `Z(Q(a)) = a XOR (bit0(a) ? 1 : 0)` | Projection onto the fixed-free-coordinate subspace |
| `traceBit(Q(a)) = 0` | Trace-one inputs have no quadratic preimage |
| `bit0(Z(a)) = 0` | The chosen output fixes the free coordinate |

These imply that a solution exists exactly when trace is zero, and that the
solution whose bit zero is clear is unique. No irreducibility premise or
successful-source-call premise is hidden in these word-model results.

## Actual source maps

The new native endpoints quantify every U64 input and use the actual extracted
Gf64 dictionary. The original generic fallback branches remain in the generated
bodies.

- `trace` returns normally with the complete selector byte, then its zero
  extension is linked to the independent conjugate-sum word trace.
- `canonical_trace` proves the original 63-step loop. Its sum/conjugate invariant
  and decreasing remaining count establish normal termination. The proved
  zero/one sum discharges the real assertion and checked U8 conversion.
- `quadratic_rows` returns the exact 64-entry source slice normally.
- `quadratic_value` proves every original chunk iteration, lossless pointer-width
  conversion, index bound, constant shift by four, accumulator prefix and
  terminal `None`. Its complete output equals the independent matrix map.
- `solve_quadratic` returns normally on all words: trace one returns `None`;
  trace zero returns the correct root with bit zero clear, unique among roots
  satisfying that normalization. The original square/assertion is proved safe.

The additional standard-library models use general checked unsigned conversions
and exact population counts. The pinned runtime already represents integer
conversion errors as Unit and erases formatting in `expect`; the adapter's
diagnostic behavior is not claimed as Rust formatting correctness. Independence
from every Debug dictionary is proved, and all endpoint conversions establish
inner `Ok` before `expect`.

## Remaining scope

This establishes the literal Mathlib polynomial theorem and the specified word
and native-source refinements. The formal native-word-to-polynomial quotient
field representation, field-law transport and identification with Mathlib's
`Algebra.trace` remain separate obligations.

Inverse functions remain unproved. The original enclosing inverse extraction
fails on the captured borrowed-square closure; its failure is preserved. A
standalone original `inverse_with_frobenius` extraction succeeded, but neither
extraction nor an unintegrated projection is credited as an inverse proof.

The x86-only Frobenius lookup/table-generation paths, inversion, the decoder,
public state/resource/ownership behavior and compiler-expanded closure remain
in scope. All 344 native executable obligations are retained. The checkpoint's
14 source-body refinements and 65 frozen endpoints are distinct evidence counts,
with no full-native coverage percentage claimed.
