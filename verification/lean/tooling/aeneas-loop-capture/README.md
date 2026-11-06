# Checked immutable captures in Aeneas loops

This package records a bounded patch to Aeneas commit
`ab34bd28458a08c150b7cbf1873e59af74588138`. It changes no native BulkSketch source
and does not replace a captured application closure with a correctness model.
The original pinned Aeneas checkout remains clean and continues to supply the
Lean runtime. The patched extractor is built in a separate checkout.

## The two defects and the patch

The original nested shared capture fails when loop entry unnecessarily copies a
frozen closure loan into a new endable abstraction. Collapse correctly rejects
the resulting nested concrete shared borrow. The patch preserves the original
frozen input graph for a narrow class of immutable values instead of introducing
that copy. The existing collapse guard is unchanged.

Eligibility follows every concrete shared-borrow edge and requires a frozen
owner at each step. It rejects cycles, missing or endable referents, mutable or
reserved borrows, loan nodes, bottom values, and expandable symbolic values.
Only symbolic `TVar` leaves are admitted: an opaque generic type variable has no
constructors or fields for the interpreter to expand. Concrete aggregates and
literal leaves are traversed normally. Borrow and loan identities are preserved.
References do not hide an unchecked mutable or expandable structural referent.

This optimization is enabled **only with `-checks`**. Existing join and
fixed-point matching then require equality of frozen abstractions and their
fixed identifiers. Thus preservation cannot silently accept a changed frozen
input context. In unchecked mode, the old reborrow path and its rejection remain.
This is a reviewed translator change under the explicit extraction trust
boundary, not a kernel proof of frontend soundness.

Passing the former borrow failure exposes a separate loop-helper type defect:
generic filtering considered the normalized body expression while a constant
input's type alias still contained phantom parameters. The helper's signature
could mention `F` and `T1` after dropping their generic binders. The patch also
collects generic dependencies from the actual signature input types, at both
loop and standalone body generation. It retains correct parameters rather than
skipping annotations or inventing substitutions for missing variables.

`loop-capture.patch` modifies exactly:

- `src/interp/InterpJoin.ml`
- `src/pure/PureUtils.ml`
- `src/pure/PureMicroPassesLoops.ml`

## Regression evidence

`run.py` extracts the real regression crate with pinned Charon and runs both
baseline and patched Aeneas with invariant checks enabled. Its matrix records:

| Case | Baseline | Patched with checks |
| --- | --- | --- |
| Captured callback loop | Original guard rejection | Complete translation |
| Two aliased immutable captures | Original guard rejection | Complete translation |
| Captured callback with phantom generic parameters | Rejection | Complete translation |
| Ordinary shared loop | Complete translation | Complete translation |
| Opaque generic trait callback returning a shared reference | Rejection | Complete translation |
| Shared reference to a tuple containing `&mut u64` | Rejection | Rejection retained |
| Shared reference to a tuple containing `&u64` | Rejection | Rejection retained |
| Shared capture whose symbolic Option/tuple referent is inspected | Rejection | Rejection retained |

The last three cases are unchanged limitations, not proofs of those programs.
They specifically exercise indirect borrowed referents without weakening the
old failure policy. The patched binary without `-checks` still rejects the
original capture case. Two invalid Rust aliasing programs are separately rejected
with `E0502`; these compiler rejections supplement the actual Aeneas graph
controls. A native regression test compares callback, alias and phantom-generic
iteration outputs for multiple counts and words. These are translator tests and
give no native BulkSketch coverage credit.

Finally, the patched binary translates the **unchanged original** inverse-pilot
LLBC with `-checks -sequential`. The generated `Types.lean` and `Funs.lean` are
byte-identical to the source artifacts under
`extraction/inverse-wrappers/Arithmetic`. The receipt records the exact input,
binary, patch, modified-source, generated-file and log hashes. Successful
extraction alone is not a native proof; the separate Lean source refinements and
independent exported-term checking supply that evidence.

## Reproduction

Use a separate Aeneas checkout at the exact base commit, apply this patch with
`git apply`, and build its `src` project using the pinned Charon OCaml sources
and an OCaml 5.3 environment with Aeneas dependencies. Keep the original runtime
checkout unchanged. The recorded local command is:

```sh
opam exec --root=/Users/junbug/bulk/bulksketch-proofs/tooling/opam-root \
  --switch=aeneas-5.3.0 -- dune build \
  --root /Users/junbug/bulk/bulksketch-proof-tools/aeneas-loop-capture/src -j 2

python3 tooling/aeneas-loop-capture/run.py \
  --charon /Users/junbug/bulk/bulksketch-proofs/tooling/charon/bin/charon \
  --baseline-aeneas /Users/junbug/bulk/bulksketch-proofs/tooling/aeneas/src/_build/default/main.exe \
  --patched-aeneas /Users/junbug/bulk/bulksketch-proof-tools/aeneas-loop-capture/src/_build/default/main.exe \
  --patched-source /Users/junbug/bulk/bulksketch-proof-tools/aeneas-loop-capture \
  --output /Users/junbug/bulk/bulksketch-proof-tools/capture-regressions-final
```

Paths are arguments and may be changed for another machine. Native regression
source is confined to this package's separate test crate; test extraction outputs
and Cargo targets go into the chosen output directory. `receipt.json` is pinned
evidence from the recorded run. Ordinary proof verification checks its source
and artifact bindings without requiring OCaml, Charon or a patched extractor.
