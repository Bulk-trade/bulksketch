# Original Berlekamp–Massey locator extraction

The original `bulksketch::decode::bm::locator` LLBC is complete. The
checked source-scoped translator emits three exact Lean artifacts.
`Arithmetic.BmLocatorGenerated` retains the locator and all 24 loop
definitions verbatim. This package has no locator functional theorem
and adds zero native-body proof credit.

## Scoped translator

`checked-bm-locator.patch` applies to the pinned Aeneas commit
`ab34bd28458a08c150b7cbf1873e59af74588138`. It requires
`BULKSKETCH_BM_LOCATOR=1` and `-checks`. Its source span gates
restrict the changes to the original locator. The supported input is
the exact `arithmetic.llbc` in this directory. The pinned Lean
runtime checkout remains clean.

The checked preprocessing distributes only the terminal
`StorageDead*; Return` suffix into the original tail switch arms,
outside loops. It then applies stock loop-exit lowering. The checked
context matcher handles identical ended loans using the established
shared scalar rule and an exact symbolic-slice case. It preserves
the original labels and registers the symbolic mapping.

Two source points match the original shared and mutable projection
components structurally, rather than relying on symbolic IDs from
one visit. The checked selectors resolve exact mirrored projection
slots and the indexed connection borrow, require live marker-free
ownership and exclude other active uses. They use stock
`end_abs_set` and compose its backward continuation. The shared
endings preserve every real binding. The mutable endings restore
the connection and preserve every other real binding. Stock
expansion and join code is unchanged.

The existing Dense shared-only erasure guard applies to two
data-free level-one endings. The mutable lowering only applies to
the matched level-one end, snapshot, loop level-zero end and mirror
level-zero end. It compares the exact typed continuations and the
matching ended metadata on both sides. It requires the nested
symbols to be absent from active contexts and unused after both
matched ends. It retains the stock level-zero assertion for other
cases.

The four retained mutable pairs preserve both typed calls. In the
first case the loop consumes Zip 5132 and binds Zip 5142. The mirror
then consumes 5142 and restores IterMut 5140. The generated caller
applies the loop backward function and the Zip constructor backward
function in that order, then restores the mutable slice. See
`Arithmetic/Funs.lean:2251–2269`.

## Exact Lean projection

The compiled projection reuses the generated backend dictionaries,
WorkMeter and WorkSchedule, inclusive-prefix indexing and existing
shared, reverse and mutable iterator bindings. Local syntax routes
the two exact original Zip dictionary heads to their existing
operations. It rejects other dictionary heads. The scoped
`BmLocatorRuntime.inclusiveRange` uses the pinned safe inclusive
range semantics over the existing exclusive Range operations,
including the end bound and exhausted-start rule. Raw pointer
operations delegate to the pinned unsafe Range model and do not
occur in the locator path.

`project.py` checks the source and tool pins, the selected LLBC
function and its original source text, the mandatory translation
flags and environment, exact raw artifact digests, reused generated
declarations, scoped runtime hashes and the 25 copied declarations.
`Axioms.lean` checks the transitive axioms of the locator definition
and the two new scoped bindings. Only the standard three occur.
This axiom audit is for definitions and does not certify the
locator algorithm.

## Replaying the translator

Use a separate checkout of the pinned Aeneas commit and apply the
patch there. Link its `charon` directory to the pinned Charon
sources and build the `src` project in the pinned OCaml environment.
From `verification/lean`, run:

```sh
python3 extraction/bm-locator/replay.py \
  --patched-source /workspace/bulk/bulksketch-proof-tools/aeneas-bm-locator-v1 \
  --output /workspace/bulk/bulksketch-proof-evidence-20261109/bm-locator-package/replay
python3 extraction/bm-locator/project.py
```

Use a fresh output directory. The replay runs both checked
translations, a disabled-mode and unchecked locator control, and
the unrelated checked Portable XOR control against the clean
baseline. The checked artifacts must match all three preserved
files. Both negative runs retain the stock early-return rejection.
The unrelated XOR artifacts match byte for byte. The replay writes
its receipt and logs in the output directory.

## Functional proof boundary

The [current checkpoint](../../NATIVE_BM_DEGREE_PROBE.md) checks the original
discrepancy, scaling, shifted XOR, normalization and reversal, and exact
entry and named active branch semantics. The full successful update and
outer connection/previous-row recurrence still need proof. This
extraction carries no full locator body credit.
