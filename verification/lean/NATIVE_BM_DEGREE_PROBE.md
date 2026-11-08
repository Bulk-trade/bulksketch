# Native degree probe and Berlekamp–Massey loop proofs

This checkpoint retains all 344 native executable obligations. The ledger
records 102 original Aeneas body refinements under their stated contracts
and five separate source-linked LLBC contracts. Production Rust is unchanged.

## Original degree probe

The original constructor, stage accessor, count conversion and rejection
transition have exact source refinements. The original `run` phase
equation covers the six admitted phases for degrees three and four:
guard, normalization, leaf solve, factor certificate, verification and
canonicalization. The theorem retains the original pricing call and
exact meter transition, including either charge error with the original
state and workspace.

The phase proof composes the original Newton guard, normalize, solve,
certificate and verification calls. It checks their source scratch windows,
candidate count conversion and rejection transitions. The unsigned
canonicalization binding gives the exact sorted permutation in the active
root prefix and the original scratch tail. The generic theorem assumes the
exact GF64 arithmetic and verification encoder contracts and phase-specific
slice, denominator and count bounds. The Portable specialization supplies
the encoder contract for the default encoder with Portable insertion.

The checked original module projection retains 14 source declarations and
two closure types verbatim, with checked shared declarations. It uses
the reviewed nested-slice retry from the Newton guard and three scoped
standard-library bindings for fold, checked conversion and sorting.
The extension gate ties the replay to the exact original LLBC and the
reviewed guard translator.

## Original Berlekamp–Massey locator

The full original locator extracts and elaborates, with all 25 generated
declarations retained verbatim. The reviewed source-scoped translator
requires checks and the explicit BM flag. The paired lowering retains the
loop's typed mutable writeback and the mirror that restores its iterator.
The stock join and expansion modules remain unchanged. The checked
replays, disabled and unchecked controls, and unrelated Portable XOR
compatibility run are frozen with the projection.

The checked source endpoints cover:

- Exact price of `6 * (budget + 1) + 128`,
  including intermediate overflows. The original checked addition
  helper has its own exact source proof.
- The original pricing and initial charge exits, the three scratch
  splits and connection and previous-row initialization, with the
  original outer loop as the continuation.
- Both original discrepancy loops, all scaling and shifted-XOR loop
  instances, and final inverse scaling. The mutable proofs give the
  exact returned backward functions. The two writeback calls compose
  to the exact destination slice and preserve the remaining frame.
- The accepted connection-row update composes the original scaling,
  inclusive zero-fill and shifted-XOR loops in source order. Its exact
  slice equation includes an empty fill interval and both writebacks.
- Both accepted nonzero branches return exact connection, previous and
  saved rows, the four scalar state values, and the charged meter.
- The exhausted-range branch, invalid-locator guards, normalization,
  reversal and buffer restoration. Active branches check charge failure,
  odd-index skipping, even zero discrepancy and degree-budget rejection.
- The scalar shift window invariant in the arithmetic state model.
  It derives the shifted interval and machine bounds from the step and
  growth relations. Linking that invariant to the entire native outer
  loop remains open.

The parity proof shows that the true skipped discrepancy vanishes for
any reconstructed GF64 row satisfying the square relation, given a vanishing
residual at all earlier powers. The polynomial update preserves that
residual condition under the anchor equations, including the bootstrap
case. These equations still need to be linked to every native loop state.
The locator has zero full-body coverage credit. The verified subloops
and branch theorems are recorded separately.

## Verification and remaining coverage

Run `python3 scripts/verify_all.py` from `verification/lean` with the pinned
toolchain. The aggregate checks original source projections, exact frozen
types, permitted axioms, independent proof replay and provenance controls.

The degree-probe theorem gives exact admitted stage transitions. Full
decoder acceptance, fallback and caller admission, the complete BM
recurrence, general root recovery, remaining accelerated kernels and
physical memory, ISA and compiler-expanded correspondence remain open.
