import BulksketchBridge.RootTraversalRanking

namespace BulksketchBridge.RootRun

open Aeneas.Std ClosedLeafAdvance bulksketch.types bulksketch.decode.roots bulksketch.decode.scratch

set_option maxRecDepth 4096

theorem reducer_phase_step (roots : Roots) :
    PhaseStep .ReducerPreparation (remainingDirections roots) (tableStage roots) (remainingDirections roots) := by
  cases affine : roots.affine
  · simp only [tableStage, affine, Bool.false_eq_true, ite_false]
    exact .reducerTrace ..
  · cases prepared : roots.affine_ready
    · simp only [tableStage, affine, prepared, ite_true, Bool.false_eq_true, ite_false]
      exact .reducerAffine ..
    · simp only [tableStage, affine, prepared, ite_true]
      exact .reducerSplit ..

theorem preparation_phase_step (roots after : Roots) (stage : Stage)
    (success : stage = .AffineSplit ∨ stage = .AffineEnumeration) :
    PhaseStep .AffinePreparation (remainingDirections roots) stage (remainingDirections after) := by
  rcases success with rfl | rfl
  · exact .prepareSplit ..
  · exact .prepareEnumerate ..

/-- The exact GCD outcome either reaches the paid divide stage or consumes
    one of the current factor's remaining directions. Error exits are terminal. -/
def ActualGcdOutcomePhaseStep : Prop :=
  ∀ (roots : Roots) (buffers : FactorWork) (size : Usize) (next : Stage),
    (roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64) →
    (roots.affine = false → roots.direction.val < 64) →
    (outcome roots buffers size).1 = .Ok (.Ok next) →
    let after := (outcome roots buffers size).2
    PhaseStep .Gcd (remainingDirections roots) next (remainingDirections after)

theorem gcd_outcome_phase_step : ActualGcdOutcomePhaseStep := by
  intro roots buffers size next affineRank traceDirection success
  dsimp only
  by_cases proper : 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val
  · unfold outcome at success
    rw [ite_eq_left proper] at success
    simp only [core.result.Result.Ok.injEq] at success
    subst next
    exact .gcdProper ..
  · cases affine : roots.affine
    · have direction := traceDirection affine
      have nextVal : (nextDirection roots).val = roots.direction.val + 1 := by
        change (BitVec.ofNat 32 (roots.direction.val + 1)).toNat = _
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      by_cases terminal : nextDirection roots = 64#u32
      · simp only [outcome, proper, ite_false, affine, Bool.false_eq_true, terminal, ite_true,
          core.result.Result.Ok.injEq, core.result.Result.Err.injEq] at success
        cases success
      · simp only [outcome, proper, ite_false, affine, Bool.false_eq_true, terminal,
          core.result.Result.Ok.injEq] at success
        subst next
        simp only [outcome, proper, ite_false, affine, Bool.false_eq_true, remainingDirections, nextVal]
        exact .gcdRetryTrace _ _ (by omega) (Nat.sub_le ..)
    · obtain ⟨positive, bounded⟩ := affineRank affine
      have previousVal : (previousRank roots).val = roots.affine_rank.val - 1 :=
        word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
      simp only [outcome, proper, ite_false, affine, ite_true, core.result.Result.Ok.injEq] at success
      subst next
      simp only [outcome, proper, ite_false, affine, ite_true, remainingDirections, previousVal]
      exact .gcdRetryAffine _ _ (by omega) bounded

#print axioms gcd_outcome_phase_step

end BulksketchBridge.RootRun
