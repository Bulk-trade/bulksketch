import BulksketchBridge.RootWorkspaceBudget
import BulksketchBridge.AffineSubspacesAnnihilators
import BulksketchBridge.RootRun

namespace BulksketchBridge.RootRun

open Aeneas.Std BmEntry AffineSubspaces AffineSubspaceAlgebra
open bulksketch.decode.roots bulksketch.decode.scratch

/-- The source splitter reads exactly one annihilator row from the
    table after the fixed-stride pending-factor region. -/
theorem affine_window_is_row (roots : Roots) (factors : Slice U64)
    (positive : 0 < roots.affine_rank.val) :
    ClosedLeaf.region factors (affineStart roots) (affineStop roots) =
      row (tail factors (roots.stride.val * roots.stride.val)) (roots.affine_rank.val - 1) := by
  let rank := roots.affine_rank.val - 1
  let stride := roots.stride.val * roots.stride.val
  have start : affineStart roots = stride + AffineSubspaces.offset rank := rfl
  have stop : affineStop roots = stride + AffineSubspaces.offset (rank + 1) := by
    rw [affineStop, start, AffineSubspaces.offset_succ]
    dsimp only [rank]
    omega
  rw [start, stop]
  apply Slice.ext
  simp only [row, ClosedLeaf.region, tail, Slice.from_val, List.slice]
  change (factors.val.drop (stride + AffineSubspaces.offset rank)).take
      (stride + AffineSubspaces.offset (rank + 1) - (stride + AffineSubspaces.offset rank)) =
    ((factors.val.drop stride).drop (AffineSubspaces.offset rank)).take
      (AffineSubspaces.offset (rank + 1) - AffineSubspaces.offset rank)
  rw [List.drop_drop]
  congr 1
  omega

theorem affine_window_of_budget (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (admitted : BudgetBuffers workspace capacity budget)
    (stride : roots.stride.val ≤ budget + 1)
    (rankBudget : roots.affine_rank.val ≤ budget) (rankMax : roots.affine_rank.val ≤ 64) :
    paidAffineReady roots workspace := by
  intro nonzero
  have rankPositive : 0 < roots.affine_rank.val := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply nonzero
    exact UScalar.eq_of_val_eq zero
  have tableRoom := subspaces_room_of_budget roots workspace capacity budget admitted stride rankBudget
  refine ⟨rankMax, ?_⟩
  have stop : affineStop roots =
      roots.stride.val * roots.stride.val + AffineSubspaces.offset roots.affine_rank.val := by
    have succ : roots.affine_rank.val = (roots.affine_rank.val - 1) + 1 := by omega
    conv_rhs => rw [succ, AffineSubspaces.offset_succ]
    change roots.stride.val * roots.stride.val + AffineSubspaces.offset (roots.affine_rank.val - 1) +
      roots.affine_rank.val = _
    omega
  rw [stop]
  have mono := AffineSubspaces.offset_mono (by omega : roots.affine_rank.val ≤ roots.affine_rank.val + 1)
  omega

#print axioms affine_window_is_row

end BulksketchBridge.RootRun
