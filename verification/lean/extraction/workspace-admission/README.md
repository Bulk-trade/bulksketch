# Original workspace admission

The pinned Charon extraction selects `bulksketch::decode::stages::check_workspace`
on x86-64 Darwin. Its structured LLBC contains the complete native body and
both checked-arithmetic closures. The original Aeneas extraction stops at the
nested mutable-borrow uniqueness guard when symbolically reborrowing the
shared `RowWorkspace`. The proof uses a scoped LLBC projection.

The projector follows the original assignments, locals, calls, enum and
Boolean branches, and terminal outcomes. It interprets the original
`checked_add` and `checked_mul` calls with the target's 64-bit `usize` bound,
`Option::ok_or` and `Result` branching with their exact variants, and shared
slice metadata and `len` as read-only length observations. It follows the
original short-circuit conditions. The two symbolic success paths give the
zero-budget and nonzero-budget predicates. The other 34 symbolic paths
return `ScratchTooSmall`. Division in the body has a positive constant
denominator. The projected program preserves the complete input workspace.

The Lean theorem proves that the projected Rust result agrees with the
independent workspace-size predicate and that the frame is unchanged. A
second theorem extracts the doubled capacity bound and the required
syndrome-slice size from admission. The caller can instantiate the
workspace length projection with its concrete nine slice lengths.

The projector uses the pinned, type-checked Charon LLBC and a frozen
registry of types, callee signatures, and source metadata. The supported
Rust standard-library semantics and the Python projection are source-link
trust boundaries. The model assumes an existing valid shared workspace
and valid slice metadata. It covers the native normal return paths,
including arithmetic overflow reported through `ScratchTooSmall`.

The aggregate verifier records this result as an LLBC projection.
The projector reports the generated-program digest and zero Aeneas body
credit. The control runner emits one `rejected` record per mutation and
retains the corresponding diagnostic.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 verification/lean/extraction/workspace-admission/project.py
PYTHONDONTWRITEBYTECODE=1 python3 -O verification/lean/extraction/workspace-admission/check_controls.py
cd verification/lean/bridge
CI=1 MATHLIB_NO_CACHE_ON_UPDATE=1 LEAN_NUM_THREADS=2 lake build BulksketchBridge.WorkspaceAdmission
```
