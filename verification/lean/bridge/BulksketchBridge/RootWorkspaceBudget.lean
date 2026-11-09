import BulksketchBridge.WorkspaceAdmission
import BulksketchBridge.RootRunSpec
import BulksketchBridge.AffineMultipleBounds
import BulksketchBridge.AffineSubspaces

namespace BulksketchBridge.RootRun

open Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.decode.roots bulksketch.decode.scratch

def workspaceLengths (workspace : RowWorkspace) : WorkspaceAdmission.Lengths :=
  ⟨workspace.syndromes.length, workspace.bm.length, workspace.polynomials.length, workspace.factors.length,
    workspace.square_table.length, workspace.verification.length, workspace.roots.length, workspace.raw.length,
    workspace.stack.length⟩

structure BudgetBuffers (workspace : RowWorkspace) (capacity budget : Nat) : Prop where
  bm : 4 * (capacity + 1) ≤ workspace.bm.length
  polynomials : 8 * (budget + 1) ≤ workspace.polynomials.length
  factors : 2 * ((budget + 1) * (budget + 1)) ≤ workspace.factors.length
  squareTable : RootSetup.tableCount budget ≤ workspace.square_table.length
  raw : 2 * (budget + 2) ≤ workspace.raw.length
  roots : budget ≤ workspace.roots.length
  stack : budget ≤ workspace.stack.length

theorem budget_buffers_of_admitted (workspace : RowWorkspace) (capacity budget : Nat) (positive : 0 < budget)
    (admitted : WorkspaceAdmission.Admitted (workspaceLengths workspace) capacity budget) :
    BudgetBuffers workspace capacity budget := by
  simp only [WorkspaceAdmission.Admitted, workspaceLengths, Nat.ne_of_gt positive, ite_false] at admitted
  obtain ⟨_, _, _, _, _, _, _, _, bm, polynomials, factors, table, _, roots, raw, stack⟩ := admitted
  exact ⟨bm, polynomials, factors, table, raw, roots, stack⟩

theorem budget_table_mono {degree budget : Nat} (bound : degree ≤ budget) :
    RootSetup.tableCount degree ≤ RootSetup.tableCount budget := by
  unfold RootSetup.tableCount
  exact Nat.mul_le_mul bound (by omega)

/-- The admitted row budget supplies the native factor-work layout and
    the complete GCD scratch for every nonleaf factor within the budget. -/
theorem gcd_buffers_of_budget (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (sized : BudgetBuffers workspace capacity budget)
    (minimum : 2 ≤ roots.degree.val) (degreeBound : roots.degree.val ≤ budget) :
    factorReady roots workspace ∧
    let work := buffersFor roots workspace
    work.modulus.length = roots.degree.val + 1 ∧
    work.trace.length = roots.degree.val ∧ work.gcd.length = roots.degree.val + 1 ∧
    4 * (roots.degree.val + 2) ≤ work.work.length ∧
    2 * (roots.degree.val + 2) ≤ work.raw.length := by
  have poly := sized.polynomials
  have table := (budget_table_mono degreeBound).trans sized.squareTable
  refine ⟨⟨by omega, table⟩, ?_⟩
  simp only [buffersFor, RootSetup.workRegions, prefix_length, tail_length,
    Nat.min_eq_left (by omega : roots.degree.val + 1 ≤ workspace.polynomials.length),
    Nat.min_eq_left (by omega : roots.degree.val ≤ workspace.polynomials.length - (roots.degree.val + 1)),
    Nat.min_eq_left (by omega : roots.degree.val + 1 ≤
      workspace.polynomials.length - (roots.degree.val + 1) - roots.degree.val),
    true_and]
  have raw := sized.raw
  omega

theorem affine_matrices_of_budget (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (sized : BudgetBuffers workspace capacity budget)
    (minimum : 2 ≤ roots.degree.val) (degreeBound : roots.degree.val ≤ budget) (budgetCap : budget ≤ capacity) :
    AffineMultiple.Layout roots.degree.val workspace.factors.length
      (workspace.bm.length - (roots.degree.val + 1)) (roots.degree.val + 1) ∧
      2 * roots.degree.val < workspace.raw.length :=
  AffineMultiple.layout_from_row_budget minimum degreeBound budgetCap sized.factors sized.bm sized.raw

/-- The table after the fixed-stride pending-factor region fits in the
    same source arena for every affine rank within the row budget. -/
theorem subspaces_room_of_budget (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (sized : BudgetBuffers workspace capacity budget)
    (stride : roots.stride.val ≤ budget + 1) (rank : roots.affine_rank.val ≤ budget) :
    roots.stride.val * roots.stride.val + AffineSubspaces.offset (roots.affine_rank.val + 1) ≤
      workspace.factors.length := by
  have square : roots.stride.val * roots.stride.val ≤ (budget + 1) * (budget + 1) :=
    Nat.mul_le_mul stride stride
  have offsets : AffineSubspaces.offset (roots.affine_rank.val + 1) ≤ AffineSubspaces.offset (budget + 1) :=
    AffineSubspaces.offset_mono (by omega)
  have triangle : AffineSubspaces.offset (budget + 1) ≤ (budget + 1) * (budget + 1) := by
    unfold AffineSubspaces.offset
    have product : (budget + 1) * (budget + 1 + 1) ≤ (budget + 1) * (budget + 1) * 2 := by
      calc
        _ ≤ (budget + 1) * ((budget + 1) * 2) := Nat.mul_le_mul_left _ (by omega)
        _ = _ := by rw [Nat.mul_assoc]
    have half := Nat.div_le_div_right product (c := 2)
    rwa [Nat.mul_div_cancel _ (by decide : 0 < 2)] at half
  have factors := sized.factors
  omega

end BulksketchBridge.RootRun
