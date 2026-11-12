import BulksketchBridge.RootTraversalPotential
import BulksketchBridge.RootNativeTraceDispatch
import BulksketchBridge.RootNativeAffineSplit
import BulksketchBridge.RootNativeGcdReborrow

namespace BulksketchBridge.RootRun

open Aeneas.Std bulksketch.types bulksketch.decode.roots bulksketch.decode.scratch

def remainingDirections (roots : Roots) : Nat :=
  if roots.affine then roots.affine_rank.val else 64 - roots.direction.val

/-- Local phase rank, below the decrease for splitting or emitting a
nonempty factor. The leading phases precede initialization of the affine
basis and do not depend on the previous rank. -/
def phaseRank (stage : Stage) (remaining : Nat) : Nat :=
  match stage with
  | .LeafThree | .LeafFour => 205
  | .FactorVerification => 204
  | .ReducerPreparation => 203
  | .AffinePreparation => 202
  | .AffineEnumeration => 201
  | .Leaf => 200
  | .Trace | .AffineSplit => 3 * min 64 remaining + 2
  | .Gcd => 3 * min 64 remaining + 1
  | _ => 0

theorem phase_rank_bound (stage : Stage) (remaining : Nat) : phaseRank stage remaining < 208 := by
  have bounded : min 64 remaining ≤ 64 := Nat.min_le_left ..
  cases stage <;> simp only [phaseRank] <;> omega

/-- All same-degree edges of the native root driver. Proper division and
nonempty emissions are charged to the larger live-degree measure. -/
inductive PhaseStep : Stage → Nat → Stage → Nat → Prop where
  | solveThree (before after : Nat) : PhaseStep .LeafThree before .FactorVerification after
  | solveFour (before after : Nat) : PhaseStep .LeafFour before .FactorVerification after
  | fallbackThree (before after : Nat) : PhaseStep .LeafThree before .ReducerPreparation after
  | fallbackFour (before after : Nat) : PhaseStep .LeafFour before .ReducerPreparation after
  | fallbackCertificate (before after : Nat) : PhaseStep .FactorVerification before .ReducerPreparation after
  | reducerTrace (before after : Nat) : PhaseStep .ReducerPreparation before .Trace after
  | reducerAffine (before after : Nat) : PhaseStep .ReducerPreparation before .AffinePreparation after
  | reducerSplit (before after : Nat) : PhaseStep .ReducerPreparation before .AffineSplit after
  | prepareSplit (before after : Nat) : PhaseStep .AffinePreparation before .AffineSplit after
  | prepareEnumerate (before after : Nat) : PhaseStep .AffinePreparation before .AffineEnumeration after
  | trace (remaining : Nat) : PhaseStep .Trace remaining .Gcd remaining
  | affineSplit (remaining : Nat) : PhaseStep .AffineSplit remaining .Gcd remaining
  | gcdProper (before after : Nat) : PhaseStep .Gcd before .FactorDivision after
  | gcdRetryTrace (before after : Nat) (smaller : after < before) (bound : before ≤ 64) :
      PhaseStep .Gcd before .Trace after
  | gcdRetryAffine (before after : Nat) (smaller : after < before) (bound : before ≤ 64) :
      PhaseStep .Gcd before .AffineSplit after
  | leafZero (before after : Nat) : PhaseStep .Leaf before .Verification after

theorem phase_step_decreases {stage next : Stage} {before after : Nat}
    (step : PhaseStep stage before next after) : phaseRank next after < phaseRank stage before := by
  cases step with
  | gcdRetryTrace before after smaller bound =>
    simp only [phaseRank, Nat.min_eq_right bound, Nat.min_eq_right (smaller.le.trans bound)]
    omega
  | gcdRetryAffine before after smaller bound =>
    simp only [phaseRank, Nat.min_eq_right bound, Nat.min_eq_right (smaller.le.trans bound)]
    omega
  | reducerTrace before after =>
    simp only [phaseRank]
    have := Nat.min_le_left 64 after
    omega
  | reducerSplit before after =>
    simp only [phaseRank]
    have := Nat.min_le_left 64 after
    omega
  | prepareSplit before after =>
    simp only [phaseRank]
    have := Nat.min_le_left 64 after
    omega
  | _ => simp only [phaseRank] <;> omega

def traversalRank (stage : Stage) (roots : Roots) (workspace : RowWorkspace) : Nat :=
  208 * traversalPotential roots workspace.stack + phaseRank stage (remainingDirections roots)

/-- A native root transition that either lowers the live factor potential
    or follows one of the same-degree control edges strictly decreases. -/
def ActualTraversalRankDecreases : Prop :=
  ∀ (stage next : Stage) (roots after : Roots) (workspace written : RowWorkspace),
    (traversalPotential after written.stack < traversalPotential roots workspace.stack ∨
      (traversalPotential after written.stack = traversalPotential roots workspace.stack ∧
        PhaseStep stage (remainingDirections roots) next (remainingDirections after))) →
    traversalRank next after written < traversalRank stage roots workspace

theorem traversal_rank_decreases : ActualTraversalRankDecreases := by
  intro stage next roots after workspace written step
  unfold traversalRank
  rcases step with smaller | ⟨same, phase⟩
  · have bound := phase_rank_bound next (remainingDirections after)
    omega
  · have lower := phase_step_decreases phase
    omega

#print axioms phase_step_decreases
#print axioms traversal_rank_decreases

end BulksketchBridge.RootRun
