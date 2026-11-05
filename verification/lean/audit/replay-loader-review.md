# Independent review of the thin Lean export replay loader

Review date: 2026-11-04. Reviewed `verification/lean/tooling/ReplayExport.lean` against the installed Lean 4.35.0 sources `Lean/Replay.lean`, `LeanChecker.lean`, `LeanExport/Parse.lean`, `LeanExport/Basic.lean`, `Lean/Declaration.lean`, `Lean/Expr.lean`, and `Lean/Environment.lean`.

This review changed no driver, proof, native Rust, frozen proposition or axiom-policy source. At root's explicit request it constructed and ran one benign policy regression using copies of existing export artifacts, preserving the originals. Root owns the loader correction, seven-fixture suite, freezing and integration.

## Verdict

**The reproduced subset-policy defect has been fixed, and no remaining blocker was identified for this controlled-source replay role.** The new guard requires every prelude declaration to exist in the original main export and match structurally before either phase is replayed. The loader retains the original parser, trust-zero kernel addition, constructor/recursor checking and quotient handling. It changes loading order without changing any declaration or the original main export.

This approval is for the stated pinned-export workflow. It is not a claim that this local driver is a sandboxed Comparator or an arbitrary hostile-export validator. The pre-existing name-only foundation-axiom policy boundary is recorded below.

## Why loading order is the relevant issue

`Lean.Kernel.Environment.replay` schedules dependencies using `ConstantInfo.getUsedConstantsAsSet`. A string literal expression carries its literal data rather than an explicit `.const String.ofList` dependency. The reported stock-checker error is therefore an implicit-literal dependency scheduling failure, not evidence that a project theorem was repaired or weakened.

The two-phase loader obtains the literal helpers and their existing core closure from an exact subset of the original exported environment. Both phases call the unchanged `Kernel.Environment.replay`. The original main input is independently replayed by Nanoda; it is not rewritten into the helper ordering or replaced by a different export for that check.

## Reproduced defect and resolution

The initial driver checked structural identity only while iterating main declarations that were also present in the prelude. It did not require all prelude declarations to belong to main. The advertised “ordering-only exact subset” policy was therefore not enforced.

The review produced an actual RED regression:

- Original main: `bridge/audit/results/review-original-bridge.export.ndjson`, SHA256 `9c062f688253c8a359a0d3347377b844ed3c0bd11c701587bbda2da3f423c6b5`.
- Exact subset prelude: `bridge/audit/results/review-exact-subset-prelude.export.ndjson`, SHA256 `ccdb6433e65e6bd56d48f1dac6fe20ab73a7c34d1873c9821b52a09b6ad7f91a`.
- Fixture: `bridge/audit/results/replay-negative/extra-prelude-before-fix.ndjson`, SHA256 `a5b831e927cc3de996e836b4ec6f53043a0e0ec722f80bbb29444367ff4a51e0`.

The fixture appends a copy of the valid closed `String.ofList` definition renamed to existing export name ID6, `u`, which was not a declaration in the original main export. Only the declaration's `name` and singleton `all` fields changed. No axiom, proposition, project proof or original input artifact changed.

The old native loader accepted it with exit0 in3.596s and reported378 prelude declarations,6701 replayed main declarations and377 identical duplicates. That is an observed policy failure, **not a claim that it accepted an invalid mathematical proof**: the extra definition was deliberately kernel-valid and conservative. Logs and full metadata are in the fixture's `.log` and `.json` siblings.

Root added the missing pre-replay loop:

1. For every submitted prelude entry, require a same-name main entry.
2. Require `sameConstant original submitted` before loading.
3. Reject missing or conflicting entries with an explicit diagnostic.

I independently re-read this corrected source. Root's updated seven-case regression record was also read: all seven expected rejections passed, including the new extra-prelude case with diagnostic `prelude: declaration absent from main export`; all original exports remained unchanged. The reviewed corrected driver source SHA256 was `fc254c50b77e31a100c9c3cf81ee3d7bd1732ba639dbf676ff080999c6178064`.

## Kernel/environment boundary

The driver parses both files with the original `LeanExport.parseStream`, which reconstructs plain maps rather than inserting anything into the process environment. The parser rejects duplicate declaration names and duplicate name/level/expression indices. It derives each map key and each `ConstantInfo.name` from the same parsed name, so no separate key/name alias bypass was found.

The replay target is created with `Lean.mkEmptyEnvironment` at its default trust level0. Its constant map starts empty. Importing `Lean.CoreM` into the driver executable does not import the driver's project environment into that target kernel environment. No project theorem is accepted through loading a prebuilt `.olean` into the replay target.

The original replay implementation passes ordinary definitions, theorems, axioms and opaque values to `Kernel.Environment.addDeclCore`. Inductives are reconstructed and checked by the kernel; constructors and recursors are compared with kernel-generated objects afterwards. The thin driver does not introduce a new add-declaration path, axiom constructor, unsafe cast, custom reduction rule or private proof assumption.

## Safety/partial declarations

Upstream replay skips constants marked unsafe or partial. The driver rejects either flag in both inputs *before* replay, preventing a silently skipped declaration from being counted as checked. The source checks cover definition safety and the unsafe fields of axioms, opaque declarations, inductives, constructors and recursors through the upstream `ConstantInfo.isUnsafe`/`isPartial` methods.

A theorem whose value refers to an omitted unsafe/unknown declaration is still subject to ordinary kernel checking in the fresh target environment. No code from the serialized proof is evaluated as an IO program or elaborator plugin by this parser/replay route.

The negative-suite record confirms rejection of unsafe and partial real project declarations as separate cases. A process success code is emitted only after both replay phases and their postchecks finish; exceptions return failure.

## Duplicate handling

Two distinct comparisons are correctly retained:

- **Original main versus submitted prelude:** `sameConstant` combines full derived ConstantInfo equality with structural expression equality for types and all available definition/theorem/opaque values. It additionally checks recursor rule RHS structure. Derived record equality already checks rule-list lengths, so the additional `zip` does not allow a differing-length suffix to escape.
- **Submitted prelude versus checked kernel object:** upstream ConstantInfo equality is used. Its Expr comparison is alpha-equivalence and ignores binder names/annotations, as explicitly documented in Lean's `Expr.lean`. This permits the kernel's legitimate regenerated recursor binder names without changing kernel meaning.

A main entry is removed from the second phase only after the submitted original data matches it structurally and the checked kernel object matches that submission by the upstream comparison. In particular theorem and opaque values are included; a same-type, different-proof declaration is not silently removed merely because a theorem with that name/type already exists.

Upstream replay has its own duplicate-private-theorem handling based on name/type/universes/mutual metadata. The driver's stronger comparison protects the intentional cross-phase duplicates before delegating the remaining map. This review found no added type-only duplicate shortcut.

The negative conflicting-preload test mutates a real `String.ofList` value while leaving its name/type; the corrected loader rejects it. This is relevant to the actual skipped-duplicate path rather than only testing an unrelated malformed proof.

## Quotients and kernel-generated data

`Declaration.quotDecl` generates `Quot.mk`, `Quot.lift` and `Quot.ind` itself. The loader removes those three entries before each phase and verifies their submitted ConstantInfo objects against the resulting kernel objects afterward, including `Quot` when present. It also checks the original full main quotient objects after the final replay. This follows the installed upstream `LeanChecker.checkExport` procedure rather than accepting unexamined exported quotient rule bodies.

Constructors/recursors retain upstream postponed validation against kernel-generated objects. No quotient or recursor acceptance bypass was added by this loader, and no new quotient rules were introduced. This is source reasoning under the original valid export/controlled-source scope; no additional malformed-quotient exploit test was run or claimed.

## Axiom policy boundary

Both inputs reject axioms outside the three permitted names `propext`, `Quot.sound`, `Classical.choice`. Private/application correctness axioms are not added or permitted. The negative-suite record includes forbidden axioms in main and prelude separately.

This is a **name whitelist**. By itself it does not establish canonical foundation-axiom signatures or all definitions referenced by those signatures for an arbitrary adversarial export. That boundary predates the loader and is not solved by kernel checking a well-typed axiom declaration. In this workflow the standard declarations come from the pinned original Lean environment and the trusted source/frozen-challenge/export provenance; the prelude now cannot extend that declaration set.

Accordingly retain the existing claim: controlled-source exact-statement/axiom auditing plus replay through Lean and independent Nanoda. Do not describe this loader alone as a sandboxed arbitrary-input proof validation service. No unrun foundation-forgery exploit is claimed here, and this review requests no change to the approved standard-axiom policy or frozen mathematical specifications.

## Evidence inspected and remaining work

The reviewed negative-suite record reports expected rejection for:

1. Invalid real project proof value.
2. Conflicting preloaded core definition.
3. Unsafe project declaration.
4. Partial project declaration.
5. Extra valid prelude declaration absent from main.
6. Forbidden main axiom.
7. Forbidden prelude axiom.

Original export hashes were preserved. The prior positive two-phase replay and original-export Nanoda replay were reported by root; this review directly ran the original subset-policy RED case and inspected the updated seven-case GREEN record. Root owns final positive aggregate rerun and integration after freezing the corrected driver/reproduction scripts.

No remaining review blocker was identified after the strict subset guard. Preserve the loader source/version/hash, both original input hashes, selected exact-subset metadata, all replay logs and the explicit controlled-source/runtime boundaries in the final verification record.
