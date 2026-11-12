# Native reconstruction and workspace admission

The source inventory retains 344 native executable obligations. The associated
record contains 87 original Aeneas body refinements under their stated contracts and five
separate source-linked LLBC contracts. The production Rust source is unchanged.

## Exact reconstruction

The original `Execution::reconstruct` checks whether both budgets are equal
and all difference words are zero. In that case it charges zero and returns
without reading scratch lengths. The proof retains the already-exhausted
meter case. Every other path first prices reconstruction and charges the
meter. A pricing or charge error preserves the workspace. A workspace
rejection preserves the workspace and returns the meter after charging.

For admitted scratch, the wrapper writes the sentinel zero at index zero
before invoking one of the two original inclusive-range loop instances.
The iteration at index (i) copies
difference word (i/2) when (i) is odd and squares the previously
written syndrome at (i/2) when (i) is positive and even. The checked
range proof covers both reads, every write and the multiplication of
capacity by two. The final result preserves the execution state, the
untouched syndrome suffix, every other workspace field and the identity
backward projection. The arithmetic callback must agree with GF64 squaring.

The exact wrapper and both loops use the pinned checked ended-projector
leaf matcher. The raw original source declarations and local all-zero
closure are preserved verbatim. The checked slice iterator binding evaluates
the original predicate in order and short circuits, retaining the consumed
offset. The workspace call binds to the separately checked LLBC model.
The scoped projector checks all these source and shared declaration links.
Replaying checked Aeneas reproduced all three raw Lean artifacts byte for
byte. Pinned and unchecked controls reject the same original LLBC join.

For a difference row representing the odd power sums of a support, the
successful paid stage returns the exact positive power sums through twice
capacity. In characteristic two, squaring the power sum at (i/2) gives
the power sum at even (i). Strong induction over the checked recurrence
combines that fact with the odd input words. The theorem composes the
original stage with the existing Mathlib quotient-field bridge.

## Read-only workspace admission

The separately checked `check_workspace` LLBC model uses nine lengths
from the original workspace. Its projector follows the original checked
arithmetic and short circuit paths. The contract preserves the complete
descriptor. The
independent success predicate covers the zero and nonzero budget cases.
Every rejected path returns `ScratchTooSmall`. On success the exact length
requirement provides the (2c+1) syndrome slots needed by reconstruction.

The original workspace LLBC is transparent in this separate extraction.
The pure Aeneas emitter still rejects the shared reborrow of a structure
containing live mutable slices. The projector checks the typed original
normal paths and their read-only access. It validates the calls to both
original checked arithmetic closures. The source receipt preserves that
boundary and the failed Aeneas diagnostic.

## Work schedule

The original conversion and multiplication helpers check the exact
unsigned results and the multiplication overflow error. The checked
Reconstruct pricing branch computes (3c) or returns `WorkLimitExceeded`.
The original charge wrapper preserves every pricing outcome and submits
a valid price to the previously checked finite-word WorkMeter. Its
composed Reconstruct theorem fixes the exact price, Rust result, and all
three meter fields. Other pricing branches are outside this reconstruction
contract; [root traversal](NATIVE_ROOT_RUN.md) and the [overview](README.md)
describe their work-accounting composition.

## Verification and related proofs

Run `python3 scripts/verify_all.py` from `verification/lean` using the pinned
toolchain. The aggregate includes the exact source projections, statement
types, transitive axiom audit, Lean and Nanoda replays, and source and
translator mutation controls.

The recorded Berlekamp–Massey diagnostics crossed early-return lowering,
mutable iterator expansion and the initial collapse index, then stopped at a
shared Zip projection in the shared-loan collector at
`InterpReduceCollapse.ml:80`. Those outputs are diagnostic artifacts rather
than source-refinement evidence. The [BM locator](NATIVE_BM_LOCATOR.md) and
[root traversal](NATIVE_ROOT_RUN.md) documentation describe the corresponding
function-body proofs. The [Portable theorem](README.md) establishes ordinary
no-hint end-to-end decoding with explicit input and resource assumptions.

Public input construction and request admission, the shared job and aggregate
budget, hint/V3 composition, accelerated end-to-end execution, physical pointer
provenance and compiler-to-ISA correspondence remain broader obligations.
