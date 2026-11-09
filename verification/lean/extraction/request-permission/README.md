# Request permission extraction

The original native and borrowed-row `RequestInput::permits_id` implementation
bodies are captured with Charon borrow checking and Aeneas sanity checks.
The standalone `FrozenSketch::shape` projection supplies the same captured
accessor definition. The original `SketchShape::permits_id` theorem supplies
the routing law used by both request wrappers.

The Aeneas preset's wildcard associated-type lifting warns on the unused
`RequestInput::remaining_rows` GAT. This capture runs the other preset
transforms unchanged and lifts only the standard-library `Deref` and
`SliceIndex` traits. The resulting original LLBC has `has_errors=false`.
The isolated compiler's guard permits these exact selectors and switches
with checks enabled. Its patch changes only the input-option predicate.
The separate stock run rejects the missing preset marker. The scoped
compiler rejects the no-check and wrong-lift controls. No Rust source or
LLBC post-processing is used.

`project.py` checks both original Rust files, the scoped compiler patch,
the checked LLBC, the command receipts, four byte-identical replayed
Lean artifacts, the reused frozen accessor and fourteen original type
declarations. To rebuild the translator from pinned source and replay the
capture, pass a fresh isolated path, the local Aeneas checkout and the
local opam root to `rebuild.sh`.

The ordinary request checks the requested bucket in the single local
shape. The borrowed-row request first selects its local row and checks
bucket zero in that row's shape. A missing row fails the slice bound check.
The immutable Arc dereference boundary comes from the separate frozen
shape proof. The request driver loop and GAT-backed iterator remain outside
this refinement.
