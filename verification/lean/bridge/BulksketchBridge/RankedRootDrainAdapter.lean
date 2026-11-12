import BulksketchBridge.RankedExecutionDrain
import BulksketchBridge.NativeTraversalDriver
import BulksketchBridge.RootTraversalRanking

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime ExecutionFinish RootRun
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def nativeDrainRuntime (canonicalize : Canonicalize) : DrainRuntime :=
  ⟨nativeCalls, nativeDivRem, canonicalize⟩

abbrev RootDrainState (K : Type) := DrainState bulksketch.field.Gf64 K

/-- Reserve two ranks for Verification and Canonicalization after the root
stages. The root rank itself uses the verified local phase and degree
potential, and the drain observes terminal states without another step. -/
def rootTailRank {K : Type} (point : RootDrainState K) : Nat :=
  match point.execution.state with
  | .Running .Verification => 2
  | .Running .Canonicalization => 1
  | .Running stage =>
    if rootStage stage then traversalRank stage point.execution.roots point.workspace + 3 else 0
  | _ => 0

theorem root_tail_rank_on_root {K : Type} (point : RootDrainState K) (stage : Stage)
    (state : point.execution.state = .Running stage) (root : rootStage stage = true) :
    rootTailRank point = traversalRank stage point.execution.roots point.workspace + 3 := by
  unfold rootTailRank
  rw [state]
  cases stage <;> simp_all [rootStage]

theorem verification_to_canonicalization_rank {K : Type} (before after : RootDrainState K)
    (verify : before.execution.state = .Running .Verification)
    (canonicalize : after.execution.state = .Running .Canonicalization) :
    rootTailRank after < rootTailRank before := by
  unfold rootTailRank
  rw [verify, canonicalize]
  change 1 < 2
  decide

private theorem sum_square_bound (left right : Nat) :
    left ^ 2 + right ^ 2 ≤ (left + right) ^ 2 := by
  calc
    _ ≤ left ^ 2 + right ^ 2 + 2 * left * right := Nat.le_add_right ..
    _ = _ := by ring

private theorem pending_potential_bound (stack : Slice FactorFrame) (count : Nat) :
    pendingPotential stack count ≤ pendingDegree stack count ^ 2 := by
  induction count with
  | zero => simp [pendingPotential, pendingDegree]
  | succ count ih =>
    have lhs : pendingPotential stack (count + 1) =
        pendingPotential stack count + slotDegree stack count ^ 2 := by
      simp only [pendingPotential, Finset.sum_range_succ]
    have rhs : pendingDegree stack (count + 1) =
        pendingDegree stack count + slotDegree stack count := by
      simp only [pendingDegree, Finset.sum_range_succ]
    rw [lhs, rhs]
    exact (Nat.add_le_add_right ih _).trans (sum_square_bound _ _)

/-- The initial tail's allowance depends only on the admitted degree
budget, even when pending frames already exist. -/
theorem root_tail_rank_budget {K : Type} (point : RootDrainState K) (stage : Stage) (budget : Nat)
    (state : point.execution.state = .Running stage) (root : rootStage stage = true)
    (mass : factorDegreeMass point.execution.roots point.workspace.stack ≤ budget) :
    rootTailRank point + 1 ≤ 208 * budget ^ 2 + 211 := by
  let roots := point.execution.roots
  let stack := point.workspace.stack
  have used : roots.degree.val + pendingDegree stack roots.pending.val ≤ budget := by
    unfold factorDegreeMass at mass
    dsimp only [roots, stack]
    omega
  have potential : traversalPotential roots stack ≤ budget ^ 2 := by
    unfold traversalPotential
    exact ((Nat.add_le_add_left (pending_potential_bound stack roots.pending.val) _).trans
      (sum_square_bound _ _)).trans (Nat.pow_le_pow_left used _)
  have phase := phase_rank_bound stage (remainingDirections roots)
  rw [root_tail_rank_on_root point stage state root]
  change 208 * traversalPotential roots stack + phaseRank stage (remainingDirections roots) + 3 + 1 ≤ _
  omega

/-- This is the source-stage certificate consumed by the generic drain.
The local root proof supplies a proper potential decrease or an exact
same-degree phase edge. A transition into Verification leaves the root
lane and therefore decreases without a further potential premise. -/
def RootDestinationProgress {K : Type} (before after : RootDrainState K) (stage next : Stage) : Prop :=
  next = .Verification ∨
    rootStage next = true ∧
      (traversalPotential after.execution.roots after.workspace.stack <
        traversalPotential before.execution.roots before.workspace.stack ∨
       (traversalPotential after.execution.roots after.workspace.stack =
          traversalPotential before.execution.roots before.workspace.stack ∧
        PhaseStep stage (remainingDirections before.execution.roots)
          next (remainingDirections after.execution.roots)))

theorem root_destination_lowers_rank {K : Type} (before after : RootDrainState K) (stage next : Stage)
    (state : before.execution.state = .Running stage) (nextState : after.execution.state = .Running next)
    (root : rootStage stage = true) (progress : RootDestinationProgress before after stage next) :
    rootTailRank after < rootTailRank before := by
  rw [root_tail_rank_on_root before stage state root]
  rcases progress with terminal | ⟨nextRoot, ranked⟩
  · unfold rootTailRank
    rw [nextState, terminal]
    change 2 < traversalRank stage before.execution.roots before.workspace + 3
    omega
  · rw [root_tail_rank_on_root after next nextState nextRoot]
    have lower := traversal_rank_decreases stage next before.execution.roots after.execution.roots
      before.workspace after.workspace ranked
    omega

/-- Lift the exact original root wrapper, including its charge rejection
and decoder failure paths, into the generic drain step. Only successful
root continuations require the stage-specific invariant and progress. -/
theorem ranked_step_of_native_root_return {K : Type} (canonicalize : Canonicalize)
    (kernels : BulkKernels K bulksketch.field.Gf64) (input : RowInput)
    (admitted : RootDrainState K → Prop) (before : RootDrainState K) (stage : Stage)
    (reply : RootReply) (roots : Roots) (written : RowWorkspace)
    (back : RowWorkspace → RowWorkspace) (paid : WorkMeter)
    (state : before.execution.state = .Running stage) (noProbe : before.execution.degree_probe = none)
    (root : rootStage stage = true)
    (ran : Roots.run nativeCalls nativeDivRem RootSetup.gf64Dictionary kernels before.execution.roots
      stage before.workspace before.meter = .ok (reply, roots, written, back, paid))
    (continues : ∀ next, reply = .Ok (.Ok next) →
      let after : RootDrainState K := ⟨{before.execution with state := .Running next, roots := roots}, written, paid⟩
      admitted after ∧ RootDestinationProgress before after stage next) :
    RankedDriverStep (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
      admitted rootTailRank before := by
  have source := native_root_driver_return canonicalize kernels before.execution stage input before.workspace
    before.meter paid reply roots written back state noProbe root ran
  cases reply with
  | Err error =>
    exact ⟨.Err error, ⟨{before.execution with state := .Error error, roots := roots}, written, paid⟩,
      back, source, trivial⟩
  | Ok reply =>
    cases reply with
    | Err failure =>
      exact ⟨.Ok (progress stage {before.execution with roots := roots}),
        ⟨{before.execution with state := .Failed failure, roots := roots}, written, paid⟩,
        back, source, .inl rfl⟩
    | Ok next =>
      let after : RootDrainState K :=
        ⟨{before.execution with state := .Running next, roots := roots}, written, paid⟩
      obtain ⟨safe, ranked⟩ := continues next rfl
      exact ⟨.Ok (progress stage {before.execution with roots := roots}), after, back, source,
        .inr ⟨safe, root_destination_lowers_rank before after stage next state rfl root ranked⟩⟩

/-- A charge rejection with an untouched root/workspace frame preserves the
exact paid meter and identity callback, and the original driver latches
the reported error. The native source stage supplies the rejection. -/
theorem native_root_charge_error_latched {K : Type} (canonicalize : Canonicalize)
    (kernels : BulkKernels K bulksketch.field.Gf64) (input : RowInput)
    (before : RootDrainState K) (stage : Stage) (error : DecodeError) (paid : WorkMeter)
    (state : before.execution.state = .Running stage) (noProbe : before.execution.degree_probe = none)
    (root : rootStage stage = true)
    (ran : Roots.run nativeCalls nativeDivRem RootSetup.gf64Dictionary kernels before.execution.roots
      stage before.workspace before.meter =
      .ok (.Err error, before.execution.roots, before.workspace, id, paid)) :
    nativeCandidateDriver canonicalize kernels before.execution input before.workspace before.meter =
      .ok (.Err error, {before.execution with state := .Error error}, before.workspace, id, paid) := by
  have source := native_root_driver_return canonicalize kernels before.execution stage input before.workspace
    before.meter paid (.Err error) before.execution.roots before.workspace id state noProbe root ran
  simpa only [transition, liftRootReply] using source

#print axioms root_tail_rank_budget
#print axioms root_destination_lowers_rank
#print axioms ranked_step_of_native_root_return
#print axioms native_root_charge_error_latched

end BulksketchBridge.ExecutionDriver
