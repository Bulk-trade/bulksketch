import BulksketchBridge.RootAffineGcdPair
import BulksketchBridge.RootAffinePreparationInvariant

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr DenseReducerAlgebra
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

/-- The stored basis from exact native affine preparation supplies every
subsequent splitter lookup, with no extra hypothesis on basis words. -/
def ActualAffineSplitReadyAfterPreparation : Prop :=
  ∀ (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (directions : Array U64 64#usize) (capacity budget : Nat)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget)
    (prepared : AffinePreparedStage .AffineSplit roots workspace directions)
    (minimum : 3 ≤ roots.degree.val)
    (correct : CorrectTable (buffersFor roots workspace).modulus
      (buffersFor roots workspace).table roots.degree.val),
    AffineSplitReady roots workspace (prefixSlice directions.to_slice roots.affine_rank.val) budget

theorem affine_split_ready_after_preparation : ActualAffineSplitReadyAfterPreparation := by
  intro locator roots workspace directions capacity budget invariant prepared minimum correct
  have rankBasis : roots.affine_rank.val ≤ (prefixSlice directions.to_slice roots.affine_rank.val).length :=
    prepared.width.symm.le
  have rankMax : roots.affine_rank.val ≤ 64 := by
    have width := prepared.width
    rw [prefix_length] at width
    have bound : directions.to_slice.length = 64 := by simp [Array.to_slice, Slice.length]
    rw [bound] at width
    omega
  have rankBudget := prepared.rankBound.trans (traversal_degree_budget locator roots workspace capacity budget invariant)
  refine ⟨prepared.affine, minimum, rankBudget, rankMax, rankBasis, prepared.independent,
    ?_, ?_, prepared.next, correct, prepared.contains⟩
  · change workspace.basis.directions.isSome
    simp [prepared.directionsEq]
  · intro i inside
    unfold basisAt
    change (match workspace.basis.directions with
      | none => 0#u64
      | some basis => basis.val[i]!) = (prefixSlice directions.to_slice roots.affine_rank.val)[i]!
    rw [prepared.directionsEq]
    simp only [prefixSlice, Array.to_slice, Slice.getElem!_Nat_eq, Slice.from_val,
      List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt inside]

#print axioms affine_split_ready_after_preparation

end BulksketchBridge.RootRun
