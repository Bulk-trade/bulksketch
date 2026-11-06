# Word quotient and trace semantic review

Date: 2026-11-06. Reviewed native source revision: `0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`.

## Independence and scope

The reviewing agent authored WordSpec, Word, WordOps, WordChallenges, WordLaws and WordEndpoints. Its analysis of these files is a self-review; the separate trace agent cross-reviewed the representation and operation proofs. This review is independent of the authors of WordSquare, WordEquiv, TraceSpec, Trace, TraceNative, WordNative and InversePower. It reviews propositions, their mathematical meaning and source composition, rather than assigning complete native-contract coverage.

## Findings

- The carrier is exactly Mathlib `AdjoinRoot (X^64 + X^4 + X^3 + X + 1 : Polynomial (ZMod 2))`; its field instance is obtained from the existing independently proved irreducibility theorem. No native arithmetic law is assumed in constructing that field.
- `wordPolynomial` uses bit index zero as the constant coefficient and every bit through width minus one. Its coefficient theorem quantifies every natural index, including positions outside the word. The injectivity argument uses the strict representative degree bound and divisibility by the monic degree-64 modulus. It does not rely on finite sampling or assume a source operation succeeds.
- The actual map is surjective because it is proved injective between finite types of the same proved cardinality. `wordFieldEquiv` uses that map as its forward function. This is a representation equivalence, not an equivalence that accidentally preserves standard numeric BitVec addition/multiplication.
- The raw multiplication proof preserves all 128 coefficients by induction on the independent convolution prefix. The widening-shift theorem is applied only when the source width plus shift fits in 128 bits. The modulus multiple retains every coefficient through degree 127. Mapping the existing division certificate into the quotient gives reduction semantics on every raw word pair.
- `wordPolynomial_rawSquare` checks all coefficients using Polynomial.expand and the characteristic-two Frobenius identity. It is independent of the previously proved word period and does not use trace or inverse correctness. Composition with reduction gives the ordinary quotient-field square.
- Field finiteness, finrank 64 and cardinality 2^64 follow from the monic power basis. Mathlib FiniteField.algebraMap_trace_eq_sum_pow is instantiated with the actual quotient; it is not a new user-defined trace. Induction transports each of the 64 conjugates. The scalar-selector theorem uses injectivity of the base-field embedding.
- Both source trace endpoints prove normal return for every U64 and bound the entire U8 output by one before relating it to Algebra.trace. This bound is material: a mere cast to ZMod 2 would otherwise fail to constrain the upper seven output bits. The canonical trace composes with its existing original-loop normal-return proof.
- Native reduction, multiplication, square and Frobenius contracts all name the real extracted Gf64 dictionary. Their normal-return equations are conclusions, not hypotheses. The Frobenius target is the full exponent 2^power.val; the old source modulo-count loop is justified by the existing universal period theorem.
- InversePower proves the total field inverse exponent, including zero. For nonzero values its two cancellations reduce the exponent equation to the independently proved power period. It neither assumes callback correctness nor converts extraction alone into an inverse wrapper proof.
- InverseSpec exposes normal-return contracts for every invocation of each supplied callback. Its expectedResult is an operational addition-chain model. This file alone is not inversion correctness and does not discharge any enclosing closure or field-arithmetic callback obligation. The final source wrapper theorem must separately supply these facts.

No semantic defect was found in the reviewed stable mathematical and source-transport propositions. Complete native contracts, ownership/compiler correspondence and all other source items remain open; this checkpoint does not establish 100% native coverage.

## Trusted boundary

The mathematical proofs use only the permitted logical foundations propext, Quot.sound and Classical.choice. Charon/Aeneas translation correctness, Rust standard-library model correspondence, compiler and machine correspondence remain the previously stated trusted boundary. No native source or pinned translator source was changed for these proofs. New generated inverse declarations and any new runtime adapters require their own exact source-linkage/model review; this report does not waive that requirement.

## Scoped independent checking

Eight fixed word endpoints were exported from BulksketchBridge.Algebra.WordEndpoints, then the same untouched original export was accepted by stock Leanchecker and independent Nanoda. No scheduling loader or modified export was needed for this mathematical subset.

```json
{
  "status": "passed",
  "roots": [
    "BulksketchBridge.Algebra.Gf64.exact_polynomial_coefficients",
    "BulksketchBridge.Algebra.Gf64.bijective_representation",
    "BulksketchBridge.Algebra.Gf64.additive_representation",
    "BulksketchBridge.Algebra.Gf64.complete_raw_product",
    "BulksketchBridge.Algebra.Gf64.reduction_representation",
    "BulksketchBridge.Algebra.Gf64.multiplication_representation",
    "BulksketchBridge.Algebra.Gf64.square_representation",
    "BulksketchBridge.Algebra.Gf64.arithmetic_field_laws"
  ],
  "checks": [
    {
      "name": "export",
      "exit_code": 0,
      "elapsed_seconds": 7.847693833522499,
      "bytes": 174439263,
      "sha256": "204c8e590b2886fa2bf77f9a3f7e406bcbb670e8cf72db7b1e930534d143d19e"
    },
    {
      "name": "stock-leanchecker",
      "command": [
        "/Users/junbug/.elan/toolchains/leanprover--lean4---v4.35.0/bin/leanchecker",
        "--silent",
        "--from-export",
        "/Users/junbug/bulk/bulksketch/verification/lean/bridge/audit/results/word-quotient-review/words.export.ndjson"
      ],
      "exit_code": 0,
      "elapsed_seconds": 15.21886175032705
    },
    {
      "name": "independent-nanoda",
      "command": [
        "/Users/junbug/.elan/toolchains/leanprover--lean4---v4.35.0/bin/nanoda_bin",
        "/Users/junbug/bulk/bulksketch/verification/lean/bridge/audit/results/word-quotient-review/nanoda.json"
      ],
      "exit_code": 0,
      "elapsed_seconds": 5.338089167140424
    }
  ]
}
```

## Reviewed file fingerprints

| File relative to bridge/BulksketchBridge | SHA-256 |
| --- | --- |
| `Algebra/WordSpec.lean` | `ab8929aa4b46148dbaf1add1f4fdb19b21de1b7c15b4edbed8f084b062db33c8` |
| `Algebra/Word.lean` | `3e215eb5e2c0e8715d6a1b292aa9b5c121745e492f2dacc6a02e794e45da72ff` |
| `Algebra/WordOps.lean` | `41a9d59672477555441f3d1e9b6f91bae5cd6845ce4f4e2d409c3fb61e28733a` |
| `Algebra/WordChallenges.lean` | `bd1baacce1fb827da2a25fa6ca35c743b07bbef3597c1d178e82af25ae44d8b8` |
| `Algebra/WordEndpoints.lean` | `89a3c83f35dcbaf1ebda13d3cca3d242298b432408a963a566e233aa82389701` |
| `Algebra/WordLaws.lean` | `3aefe6750763ed1bbcd9980f9ae8339eb988c678ff5926a33a22851e7fdc81fc` |
| `Algebra/WordEquiv.lean` | `e900033497485b6a34b863d10752e2cf462b7a2a9f95138b487e07b01b0a7396` |
| `Algebra/WordSquare.lean` | `feedc20646c9c5b37effbf9074a0cb65d3b195cb8cb7ecca5ab5000a619985e2` |
| `Algebra/TraceSpec.lean` | `b0d020053fba3dc2df6ce2c28077fe70972580db18f0a7373f91a2ff03517dec` |
| `Algebra/TraceChallenges.lean` | `2e3b710a135c204ddb5847891ad94c81bf79f4792b503ae0bfd4ec647f0495d2` |
| `Algebra/Trace.lean` | `2199a8d90458e11f36850c8ba8bbdd87fbfe4db9b5a1f52a9b30b20385c24d46` |
| `Algebra/TraceNativeChallenges.lean` | `de3bcc419d7dd562ba5e85888c12297475278b84f00373107c36b86d084b8b30` |
| `Algebra/TraceNative.lean` | `61ea031b1f42c154526729aa76fd62bfe79040adde448261abeacad4e6e42840` |
| `Algebra/WordNativeChallenges.lean` | `36454b67ea1a1e5f3e2cd19f6e5a1ac1815504f8ea71b66c8508f998b39fad55` |
| `Algebra/WordNative.lean` | `cc733fa11e671bc847c65661c1ebc5c63978f42dfbc963e0eafbc2bacbded296` |
| `Algebra/InversePower.lean` | `d043761d20fd30a38826ce0aba1916c0b421b3270a11e2e4ff8aba7c6473401c` |
| `InverseSpec.lean` | `cfab6bdd1c375b36576d4a35935137ac7883de01ea5e5c34650aa90ddc504f2c` |

## Final original inverse body review

The final `actualSourceReturnsExactChain`, `actualSourceReturnsFieldInverse` and
`nativeCallbackInstanceReturnsFieldInverse` propositions were reviewed after the
inversion agent completed them. The conditional API has explicit universal
callback equations to the actual native multiplication and Frobenius bodies.
The closed BuiltinFn instantiation discharges both equations by definitional
equality; it is not an assumed application-correctness axiom or an unsupported
source closure replaced with an opaque model.

The original reverse range processes bits 4,3,2,1,0 of target63. Its reachable
chain indices are 1,3,7,15,31,63; each doubling/appending step has the algebraic
exponent 2^k-1. The source-loop proof uses a decreasing remaining iteration
count and checks every U32 operation at these reachable indices. Zero and unit
return without invoking callbacks. The final square transports to exponent
2^64-2, already proved equal to the Mathlib field inverse. The exact option
specification is None precisely for the zero word and otherwise the unique
word represented by the quotient-field inverse.

`python3 extraction/inverse-chain/project.py` was rerun successfully: all three
inverse declaration texts remain byte-identical to the original successful
source-generated output. Shared types and dictionary/function declarations
are compared verbatim with the active Arithmetic package. The import boundary
is adapted to reuse those exact existing declarations; no generated function
body is edited. The reviewed projection SHA is
`b0f6af4467538ed607297dc3555fb8b416115722fcae8afba0860baa4b182359`.

This establishes the original `inverse_with_frobenius` body with stated callback
contracts and a closed actual-native-callback instance. It does not establish
the separately unsupported enclosing `inverse_using` captured-square closure or
its `inverse` caller. Those obligations stay in scope.

| Final inverse file | SHA-256 |
| --- | --- |
| `BulksketchBridge/InverseSpec.lean` | `cfab6bdd1c375b36576d4a35935137ac7883de01ea5e5c34650aa90ddc504f2c` |
| `BulksketchBridge/InverseFieldSpec.lean` | `dfaea9d3eda270ca1281f825a82226cca7f6c4782862e9ecefa9bd58bf13df59` |
| `BulksketchBridge/InverseChallenges.lean` | `2bbe81b72b41ae1bf26591f4edb9f1d7e32906debe1e8ea1f8ff5118893dedb4` |
| `BulksketchBridge/Inverse.lean` | `54cd6502db9913a9edbf56aa7e889946b4bd982336f6d2740eb2197a4d785e63` |
| `BulksketchBridge/InverseMath.lean` | `8a90625c159f5bcd09e2f8c02670b9deee5d86cd1597dffe64011ab8bc57e8f9` |
| `BulksketchBridge/InverseNative.lean` | `7d7ce75bbd9742896412d81538b16c0d196f90ff1f282bc74fa091a14f981696` |
| `Arithmetic/InverseGenerated.lean` | `b0f6af4467538ed607297dc3555fb8b416115722fcae8afba0860baa4b182359` |
| `../extraction/inverse-chain/project.py` | `c0bf776649e2d079695135292d7afb57f851856e922d8365fcf99650d595c697` |
