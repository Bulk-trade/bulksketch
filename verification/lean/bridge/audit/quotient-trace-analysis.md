# Quotient representation and algebra-trace analysis

Analysis date: 2026-11-06. Native source pin:
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`, Lean 4.35.0, and the existing
Mathlib pin `56a005855ea17e0b0958f73ec801ae140b0a1679`.

## Mathematical contracts

The contracts cover the word representation, arithmetic operations, square,
trace transport and inverse exponent. The independent proof-term checkers below
check all eighteen listed roots. Representation and source fingerprints are
documented in the [word quotient analysis](../../audit/word-quotient-analysis.md).

- The target is `AdjoinRoot modulus` over `ZMod 2`, with the exact modulus
  `X^64 + X^4 + X^3 + X + 1`. Its field instance is obtained from the earlier
  proved irreducibility theorem. Native multiplication supplies no field-law
  assumption.
- `wordPolynomial_coeff` identifies every coefficient, including all indices
  beyond the word width. Injectivity uses the strict degree bound below 64 and
  quotient equality modulo the monic modulus; it does not assume native field
  laws or enumerate selected operands.
- `wordPolynomial_clmulPrefix` proves every carryless-multiplication prefix as
  a polynomial product with a coefficient prefix. The shift-width proof retains
  all coefficients through index 127. The reduction bridge uses the existing
  universal division certificate and proves that the exact modulus multiple
  vanishes in the quotient. It assumes neither source success nor correctness
  of native reduction.
- The raw square proof checks the coefficient formula for all 128 positions,
  then uses polynomial expansion and the characteristic-two Frobenius identity.
  The square bridge composes that theorem with the proved reduction bridge.
- Dimension 64 follows from Mathlib's power basis for this exact quotient.
  Cardinality is derived as `2^64`; together with injectivity this proves
  surjectivity of the explicitly defined polynomial-basis map. The chosen
  equivalence's forward map remains exactly `toField`.
- The trace target is the existing `Algebra.trace (ZMod 2) Field`, not a newly
  defined trace. Mathlib's `FiniteField.algebraMap_trace_eq_sum_pow`, the proved
  dimension, and the proved square/XOR correspondence identify all 64 native
  conjugates with its algebraic conjugates.
- The native trace and canonical-trace contracts conclude normal return for
  every complete U64 input. Their output byte is bounded by one, and its value
  in `ZMod 2` equals the algebra trace. The byte bound is essential: equality
  after a cast to `ZMod 2` alone would not establish the whole output byte.
  These endpoints reuse the existing unconditional source-loop/conversion
  refinements; no successful-source-return premise is introduced.
- `inverse_power_of_period` is a general field lemma with an explicit power
  period premise. `field_power_period` discharges that premise for every value
  of the actual quotient using its proved cardinality. The inverse exponent
  theorem includes zero and uses Mathlib's total inverse. By itself it grants
  no native inversion-function coverage credit.

The word, native-composition and inverse-power proofs have the contracts
described above. Extractor, runtime, compiler,
and machine correspondence remain the documented trusted boundary. A generated
body refinement is distinct from complete native contracts and from closure of
the compiler-expanded implementation inventory.

## Scoped exported-term check

The scoped export imports `Algebra.TraceNative`, `Algebra.WordEquiv`, and
`Algebra.InversePower` and exports the following roots under the common prefix
`BulksketchBridge.Algebra.Gf64`:

`wordPolynomial_rawSquare`, `toField_square`, `word_natCard`,
`toField_surjective`, `wordFieldEquiv_apply`, `field_finrank`, `field_natCard`,
`algebra_trace_conjugate_sum`, `toField_iterateSquare`, `toField_conjugate_sum`,
`word_absolute_trace_transport`, `native_selector_trace_transport`,
`native_trace_is_algebra_trace`, `native_canonical_trace_is_algebra_trace`,
`inverse_power_of_period`, `field_power_period`, `field_inverse_power`, and
`word_inverse_power`.

Every root's transitive axiom closure contains only `propext`, `Classical.choice`,
and `Quot.sound`. All eighteen roots passed exported-term replay through the
unchanged Lean kernel and independently through Nanoda. No application axiom,
`sorryAx`, or native-evaluation axiom was admitted.

| Check | Result | Elapsed seconds |
| --- | --- | ---: |
| Build scoped modules | Passed | 1.761 |
| Print all 18 axiom closures | Passed | 3.330 |
| Export all roots and transitive dependencies | Passed | 8.825 |
| Export literal-dependency selector | Passed | 2.903 |
| Project exact original-export prelude subset | Passed | 6.072 |
| Stock Leanchecker on that prelude | Passed | 4.441 |
| Unchanged Lean kernel via the scheduling loader | Passed | 29.894 |
| Independent Nanoda on untouched original export | Passed | 12.240 |

Every subprocess retained the 120-second limit. The main export is 217,338,952
bytes with SHA-256
`c2013b824957d727aa83bbf80c70d263960bf97fb8fb76bbc0469b4dd2799445`.
The prelude is 214,231,340 bytes with SHA-256
`c30cd64df3f8fd0a614bd989adf49d55f425c59b25568b2ae0bb1b78ee35689b`.
It retains the original expression/name records, hence its size, while selecting
only the literal dependency declarations already present in the main export.
No export record is rewritten. Nanoda receives the original main export.

The combined repository verifier remains the final integration gate.

The source accounting retains 344 executable obligations. Mathematical
consequences are recorded separately from Rust source-body refinements; these
contracts do not establish whole-library coverage.
