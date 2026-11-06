# Independent native coverage integration review

Date: 2026-11-06. Reviewer: `portable_proofs` agent. The integration validator,
central fixture runner, and inverse-wrapper projector were authored by the root
agent. The reviewer authored the separate Portable projectors; those are not
claimed as independent authorship in this review.

## Findings

No blocking integration issue remains in the reviewed versions. One metadata
completeness gap was found and resolved during review: the translator gate
previously accepted an empty generated-artifact list and an alternate existing
LLBC input when its hash matched. The real receipt and frozen artifacts were
correct, so this was not a false proof result. The gate is now explicit about
the required original inverse-pilot input path and exactly two original
Funs/Types artifact paths. Empty, missing, duplicate and additional artifact
lists are rejected rather than vacuously passing a hash loop.

This is a controlled-source provenance/type/axiom and independent proof-term
checking workflow. The reviewed translator correctness remains an explicit TCB
boundary. Ordinary verification checks frozen producer receipts and retained
artifacts; it does not rebuild OCaml or re-run the extractor matrix. This review
does not claim an arbitrary-input sandbox or a formal compiler-correctness proof.

## Original obligations retained

The diff preserves the earlier exact native source and build-input fingerprint
checks, frozen-input hashes, clean pinned Aeneas runtime check, complete LLBC
`has_errors=false` checks, and whole-file generated-copy byte comparisons.
Coverage item IDs must still equal the original source inventory. Registry and
coverage evidence sets/counts must agree, and each native entry retains its
exact source-span hash, source-definition association, actual generated
function declaration, fixed proposition match and theorem/export-root inclusion.

The new code does not replace any earlier proposition or broaden the standard
axiom allowlist. All imported project theorem closures remain audited, and
Lean plus independent Nanoda replay remain mandatory. The original main export
is unchanged for independent replay. Existing replay time limits are retained.
The earlier three-declaration inverse projection is still checked by its
original strict checker and its metadata still requires count three.

## Projection counts and paired wrapper checking

Projection receipts are bound to the frozen descriptor's compiled/raw paths,
compiled/raw hashes, exact declaration count and shared-dependency-check result.
The count is now descriptor-specific, so the seven-method Portable group and
single-type wrapper group cannot be silently treated as the old count three.
Checker arguments are passed as an argv list, including `--types` for the
wrapper type projection; malformed output or any nonzero checker status fails.

The inverse-wrapper projector always checks the complete pair before emitting
either receipt: exactly 22 function/helper/dictionary declarations in their
expected order, one closure type alias, fixed import headers, every common
function/dictionary and every common type. It compares the compiled projections
to their original generated texts. `--types` only selects the returned receipt;
it does not omit function checking or accept an unchecked type alias. The
reviewer ran both CLI modes successfully and observed counts 22 and one with
the exact intended raw/compiled paths.

All projectors use explicit exceptions, including under optimized Python. The
central runner preserves every old inverse mutation and adds source body/raw,
shared type/dictionary, wrapper compiled-type and const-square raw-type cases
where applicable. Every isolated shadow is validated before mutation, and the
expected diagnostic is required after mutation. Originals are not modified.

Independent execution of the production central fixture runner passed all 40
ordinary/optimized rejection cases. Reported verbatim declaration counts were
inverse=3, Portable=7, Portable inverse=1, wrappers=22, const square=5. These are
projection sizes, not native-function coverage counts.

## Named reviewed translator gate

The reviewed variant requires its known pinned base and Charon commits, mandatory
checks flag, exact patch path/hash, exactly the three reviewed source-file paths,
matching pinned base-source hashes, unchanged collapse-guard source and a dry
`git apply --check` against the clean runtime. Its required `-checks` contract
must also occur in the recorded original extraction command. The canonical
original LLBC and exact two generated files are path/hash-bound.

Regression case names must form the complete required set with no duplicates,
including the captured/aliased/phantom/borrow-result cases, ordinary shared loop,
three indirect graph controls, unchecked-mode rejection and both Rust aliasing
controls. Expected baseline/patched outcomes and successful Rust value-regression
evidence are required. The frozen receipt pins the reviewed producer evidence;
the independent translator code review separately checked its actual patched
source hashes and the checked binary's original-source output.

Every source refinement's generated-file set is intersected with the named
projection variants. The resulting set must equal its registry attribution and
be a subset of declared variant IDs; duplicate IDs are rejected. This prevents
the two enclosing source inverses and Portable inverse from appearing as
unmodified-pinned-extractor refinements. The actual metadata attributes those
three source bodies to `checked-frozen-capture-v1`; older arithmetic and seven
Portable forwarders remain on their original source/tool provenance.

## Targeted mutation evidence

A separate review harness executes the actual validator AST gate blocks against
isolated receipt copies and the real pinned source files. It is a targeted
preflight/attribution test, not a replacement for the whole combined verifier or
proof export. Before the fix, its red table demonstrated alternate-input and
empty-artifact-list acceptance. After the fix, all 19 checks pass: three valid
contexts are accepted and 16 malformed contexts are rejected.

The invalid cases cover omitted checks in the command/contract; wrong base or
patch hash; omitted modified-source record or regression; unchecked acceptance;
wrong LLBC hash; alternate canonical input with a correct alternate-file hash;
empty/missing/duplicate/additional artifact sets; and hidden or unknown
per-refinement translator attributions. Valid old-pinned and reviewed-variant
refinement contexts both remain accepted.

Reproduction and red/green evidence are preserved outside the source tree:

- `/Users/junbug/bulk/bulksketch-proof-tools/capture-independent-review/integration_variant_gates.py`
- `integration-variant-gates-red.json` and `integration-variant-gates-green.json` in that directory
- `projection-fixtures.log` in that directory, plus the production
  `bridge/audit/results/projection-fixtures.json` result

The combined verifier remains the final integration gate. No native body credit
is granted by these validation tests, and all 344 executable source obligations
remain in scope.

## Reviewed hashes

Paths below are relative to `verification/lean`.

| File | SHA-256 |
| --- | --- |
| `scripts/verify_bridge.py` | `b52c9ca277bd18e4f281a39fec82d521b299eb50807bbae3127f401704b5f681` |
| `scripts/check_projection_fixtures.py` | `a3b6e70b3b74705644e70783c4c1d86c8a13b7146a8754259c44f3a527c6d18c` |
| `extraction/inverse-wrappers/project.py` | `63e1514ea54745c244ce1819d810f1c79ecff59ad47c840d4bb605498309dfa7` |
| `bridge/source-linkage.json` | `0a0b3f4026380f29a7ba5036f1029bd2f634cbff88d0c61545aff6d662787eb9` |
| `bridge/obligations.json` | `4effcdcf07c245e6347871b98c71ac35469889a9481b0be88b7d251cb71e56d5` |
| `tooling/aeneas-loop-capture/receipt.json` | `75073744d6a168e873ff8f86624f774c8dd462c8f13bc1a08be6ba6264830bbd` |
| `tooling/aeneas-loop-capture/loop-capture.patch` | `15ecb6d84c03d7ad68a384f10b153a1538474d813bacaeb27d4e79156cfbf111` |
