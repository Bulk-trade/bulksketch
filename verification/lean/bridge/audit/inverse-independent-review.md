# Independent inverse-source and projection review

Reviewed on 2026-11-06 by the trace-transport agent, which did not author the
inverse proofs or projection validator. The source pin remains
`0a5bda53f6b07fcae8acd870e2d0c4a246d207e6`. No native Rust or native build input
diff exists against that pin.

## Source provenance

The successful original-source extraction has `has_errors = false`, with LLBC
SHA-256 `22cc34302a68119411d0b38a31b9a627b88150159fdf4d39f0df9e24dea79e87`.
Its unedited generated `Inverse/Funs.lean` has SHA-256
`54c868d864da1a7410177e9fc2fa7e5250a4198dfb8e297b506ad436271ab397`.

The compiled `Arithmetic/InverseGenerated.lean` contains exactly the original
`inverse_with_frobenius` declaration and its two original loop declarations,
retained verbatim. Their combined text hash is
`e47c46cdb6e34ef4c06a6cc67ac7edbb86c14bccadbc1735ab06b4792045c070`.
The complete compiled projection hash is
`b0f6af4467538ed607297dc3555fb8b416115722fcae8afba0860baa4b182359`.

Only the import/type-sharing boundary is adapted. The validator checks the
original generated-file hashes, the exact complete projected text, the shared
type declarations, and every shared Gf64 function/dictionary declaration against
the active arithmetic extraction. The active generated files introduce no
additional local notation affecting the copied declarations. The ordinary
source/body hashes and unedited-copy checks remain in force.

`verify_bridge.py` runs that validator before accepting the projected generated
file. It requires the expected raw/compiled paths and hashes, the three retained
declarations, and successful shared-declaration checking. The inverse LLBC also
passes the usual source-linkage hash and `has_errors = false` gate. The projection
does not introduce an axiom for any copied application body.

The review identified one validator hardening issue: Python `assert` checks can
be disabled by optimization. The optimized-Python negative fixture reproduced
acceptance of an edited compiled body before the fix. All projection checks now
raise explicit `ValueError` exceptions. Independently rerunning the four mutations
in ordinary and optimized Python confirmed all eight expected rejections. A
valid positive projection also passed under `python3 -O`.

## Operational and mathematical review

- The proof covers every complete U64 input with the actual Gf64 dictionary.
  Its all-ones canonical mask makes the assertion normal without an input
  restriction. Zero returns `None`; one returns `Some 1` before any callback.
- `BITS - 1` is exactly 63. Leading-zero count 26, bit length 6, and the final
  subtraction establish the original reverse range `0..5`. The proof uses the
  actual runtime range/reverse iterator operations.
- Every original reverse step is proved. Its bit indices are 4, 3, 2, 1, 0;
  all are selected by target 63. Reachable `k` values are 1, 3, 7, 15, 31,
  ending at 63. Checked doubling, increment, and shifts are normal throughout.
  These are exhaustive reachable-state checks, rather than operand sampling.
- `loop_refines` decreases `5 - count` and proves the terminal iterator `None`
  case. It concludes normal completion of every reachable prefix, rather than
  assuming successful source execution or omitting the last iterator operation.
- The operational callback contracts quantify all operand words and powers.
  They describe callback outputs; they contain no inverse property and do not
  assume the enclosing inverse call succeeds. The exact-chain endpoint therefore
  preserves the generic higher-order API's explicit assumptions.
- The field endpoint requires callback calls to equal the actual generated
  multiplication and Frobenius functions pointwise. Their existing normal-result
  refinements discharge the operational callback contracts. The chain proof then
  uses the independently proved quotient-field multiplication and squaring laws.
- Each prefix denotes `a^(2^k - 1)` for the relevant `k`. The last prefix has
  `k = 63`; the final square gives exponent `2^64 - 2`. The separately proved
  quotient-field inverse law identifies that exponent with the actual inverse.
- `expectedFieldInverse` is `None` exactly at the zero word. Otherwise it is
  the unique word representing the actual Mathlib inverse, via the proved
  polynomial-basis equivalence. It does not define inverse by the chain being
  verified. The unit and nonunit cases both prove exact option/word equality.
- The callback premises are nonvacuous. A separate checked Lean example wraps
  the actual generated multiplication and Frobenius functions in the existing
  `BuiltinFn` dictionaries; both callback equalities hold by reflexivity. The
  committed `native_callback_instance` endpoint now states this closed instance
  without callback assumptions. No new runtime model is needed.

No blocking mathematical, statement, or generated-body provenance issue remains
in the reviewed checkpoint. This is a functional refinement of one original
native function body under the documented extractor/runtime/compiler/machine
boundary. The two loop helpers and additional theorem endpoints do not earn
extra native-function credit.

`inverse_using` and `inverse` remain unproved. The preserved retry evidence
records the pinned extractor's captured borrowed-square closure failure in both
loop modes. The closed `BuiltinFn` instance is not evidence that either of those
other Rust wrapper bodies has been translated or verified.

## Independent exported-term replay

The scoped export imports `BulksketchBridge.InverseNative` and includes these
ten roots under `BulksketchBridge.Inverse`:

`body_step`, `loop_refines`, `normal_refines`, `chain_index_bound`,
`chain_meaning`, `completed_chain_inverse`, `expected_result_is_field_inverse`,
`exact_chain_refines`, `field_inverse_refines`, and `native_callback_instance`.

All transitive axiom closures are subsets of `propext`, `Classical.choice`, and
`Quot.sound`. The unchanged Lean kernel and independent Nanoda both accepted
the original exported proof terms. No `sorryAx`, application correctness axiom,
or native-evaluation axiom was used.

| Check | Result | Elapsed seconds |
| --- | --- | ---: |
| Build scoped module | Passed | 1.772 |
| Print all 10 axiom closures | Passed | 3.301 |
| Separate native-callback nonvacuity example | Passed | 3.278 |
| Export roots and dependencies | Passed | 8.447 |
| Export literal-dependency selector | Passed | 3.129 |
| Project exact main-export prelude subset | Passed | 5.337 |
| Stock Leanchecker on literal prelude | Passed | 3.883 |
| Unchanged Lean kernel via reviewed scheduling loader | Passed | 23.785 |
| Independent Nanoda on untouched original main export | Passed | 11.144 |

The original export is 188,858,594 bytes with SHA-256
`5ff08c3ea4582adde4c3920a1893113113cc70892ac833b364a86a4b72047710`.
The exact-subset literal prelude has SHA-256
`ab2e99a8097037649c229f172711c730ccd84d887a5d6bb4ead50fbba887f5d0`.
Every subprocess retained the 120-second cap. The checked source hashes, complete
commands, nonvacuity example, raw exports, and logs are saved outside Git under
`/Users/junbug/bulk/bulksketch-proof-evidence-20261106/inverse-review/`.
The combined verifier remains the final integration gate.

## Reviewed source hashes

Paths below are relative to `verification/lean`.

| File | SHA-256 |
| --- | --- |
| `bridge/BulksketchBridge/InverseSpec.lean` | `cfab6bdd1c375b36576d4a35935137ac7883de01ea5e5c34650aa90ddc504f2c` |
| `bridge/BulksketchBridge/InverseFieldSpec.lean` | `dfaea9d3eda270ca1281f825a82226cca7f6c4782862e9ecefa9bd58bf13df59` |
| `bridge/BulksketchBridge/InverseChallenges.lean` | `2bbe81b72b41ae1bf26591f4edb9f1d7e32906debe1e8ea1f8ff5118893dedb4` |
| `bridge/BulksketchBridge/Inverse.lean` | `54cd6502db9913a9edbf56aa7e889946b4bd982336f6d2740eb2197a4d785e63` |
| `bridge/BulksketchBridge/InverseMath.lean` | `8a90625c159f5bcd09e2f8c02670b9deee5d86cd1597dffe64011ab8bc57e8f9` |
| `bridge/BulksketchBridge/InverseNative.lean` | `7d7ce75bbd9742896412d81538b16c0d196f90ff1f282bc74fa091a14f981696` |
| `extraction/inverse-chain/project.py` | `c0bf776649e2d079695135292d7afb57f851856e922d8365fcf99650d595c697` |
| `scripts/check_projection_fixtures.py` | `0dc011a7b556e5ae676623de89697ff63fde06fbb77df9f2f5334272b11f232f` |
| `scripts/verify_bridge.py` | `d5fe005154c6c783861cb81b651321fae9b524de23049d54d8b7ce20b6620024` |
| `scripts/verify_all.py` | `c57cfb04460626b291d42cf8a13a1c6759582e3f2dadc4765ad7fbd2a41541c5` |

All 344 executable native obligations remain in scope. Neither this review nor
the successful scoped replay establishes full native coverage.
