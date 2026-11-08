# Original quartic and candidate-copy extraction

Pinned Charon selects `bulksketch::decode::deg34::solve` with transparent
application bodies on x86-64 Darwin. The projector checks the original LLBC,
its source file and spans, and the exact quartic, solve and four generated
loop declarations. It also compares the reused affine, cubic, cube-root,
and certificate declarations with their existing compiled projections.

The checked extractor extends the ended-projector leaf variant. At the
reverse quartic loop, the initial context holds a shared roots-array index
loan and the reentry context holds the mutable update loan. A checked,
continuation-free loop fixed-point join can request the stock loan-ending
retry on the shared side. The guard requires a scalar array, an equal
shared-payload type, and a payload free of nested loans and borrows. It
keeps the mutable loan and uses the existing checked join and later
synthesis. Ordinary branch joins, collapse, and context matching keep their
existing behavior.

The receipt records the complete original extraction and byte-identical
checked replay. Pinned and unchecked runs retain the reverse-loop failure.
Eight synthetic controls check both loan orientations, rejected types and
payloads, unchecked mode, and the original matcher mode. The original cubic
and certificate extractions also remain byte-identical.

`QuarticLoops.prefix_products_refines` checks the forward loop starting
from the original array of ones. `QuarticLoops.reverse_words_refine` checks
all four reverse updates, including the saved old root used in each inverse
update. Both use the verified GF64 multiplication callback.
`QuarticSolve.solve_candidate_frames` covers the original length-four and
length-five branches with sufficient output room and the exact selected
solver call result. It returns the selected degree and candidate prefix on
a hit, preserves the output tail, and leaves the full output unchanged on
a miss.

```sh
python3 verification/lean/extraction/quartic/project.py
cd verification/lean/bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.QuarticLoop BulksketchBridge.QuarticSolve
```
