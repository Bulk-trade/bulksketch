# Checked matching of identical ended projector leaves

`checked-ended-projector-leaf-v1` applies `ended-projector-leaf.patch` to
Aeneas `ab34bd28458a08c150b7cbf1873e59af74588138` in an isolated checkout.
The Lean runtime uses the clean pinned source.

At the certificate's descending product loop, the two contexts retain the
same ended loan projector from the earlier `Iterator::any` call. The node
contains an ended symbolic ID and no consumed or borrowed descendants. The
baseline dispatcher handles live projectors, then rejects this ended node.
The checked context matcher accepts a pair only when both projector markers
are `PNone`, their types and ended IDs are identical, and both descendant
lists are empty. It preserves the ended node and leaves joins, collapses,
unchecked context matching and all live mappings on the existing paths.

To replay, apply the patch in a separate checkout of the pinned revision.
Link its `charon` directory to the pinned Charon sources. Copy `guards/`
into `src/ended_projector_guards/` and build `src` with the pinned OCaml
switch. Run the recorded `original-certificate` and `without-checks`
commands against `extraction/degree-certificate/arithmetic.llbc`. Compare
all three generated Lean files with the frozen extraction. The checked
command succeeds and the unchecked command retains the original match
failure. Run the `ended-projector-guards` command from `src` to check the
two accepted cases and six rejected cases. `receipt.json` binds the patch,
commands, guard sources, logs, and generated artifacts to their hashes.
