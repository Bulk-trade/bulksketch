import BulksketchBridge.RootEmissionProduct
import BulksketchBridge.RootFactorValidity
import BulksketchBridge.RootWorkspaceBudget
import BulksketchBridge.RootAffineTableFrame

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial
open bulksketch.decode.roots bulksketch.decode.scratch

set_option maxRecDepth 4096

/-- State that stays live during a native root traversal. The polynomial
    product tracks emitted words, the active factor, and every pending
    slot, with a separate unit interpretation for zero active degree. -/
structure RootTraversalInvariant (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (capacity budget : Nat) : Prop where
  buffers : BudgetBuffers workspace capacity budget
  degreeBudget : locator.natDegree ≤ budget
  layout : PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length
  represented : activeTraversalProduct roots workspace = locator
  mass : factorDegreeMass roots workspace.stack = locator.natDegree
  stride : roots.stride.val ≤ budget + 1
  live : liveDegree roots workspace.stack < roots.stride.val
  zeroActive : roots.degree.val = 0 → roots.pending = 0#usize
  active : 0 < roots.degree.val → ValidFactor (activeFactor roots workspace) roots.degree.val
  pending : ∀ slot < roots.pending.val, ∃ frame,
    workspace.stack.val[slot]? = some frame ∧ 1 < frame.coefficient_len.val ∧
      ValidFactor (pendingFactor workspace frame) (frame.coefficient_len.val - 1)

theorem pending_degrees_positive (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (capacity budget : Nat) (invariant : RootTraversalInvariant locator roots workspace capacity budget) :
    ∀ slot < roots.pending.val, 0 < slotDegree workspace.stack slot := by
  intro slot live
  obtain ⟨frame, exactFrame, positive, _⟩ := invariant.pending slot live
  simp only [slotDegree, exactFrame, Option.map_some, Option.getD_some]
  omega

/-- The exact native start fields and deflation's residual factor
    establish the whole positive-budget traversal invariant. -/
theorem traversal_invariant_at_start (locator residual : Polynomial Field)
    (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (buffers : BudgetBuffers workspace capacity budget)
    (layout : PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length)
    (empty : roots.pending = 0#usize)
    (stride : roots.stride.val = roots.degree.val + 1)
    (mass : factorDegreeMass roots workspace.stack = locator.natDegree)
    (degreeBudget : locator.natDegree ≤ budget)
    (represented : activeTraversalProduct roots workspace = locator)
    (residualValid : ValidFactor residual roots.degree.val)
    (active : roots.degree ≠ 0#usize → activeFactor roots workspace = residual) :
    RootTraversalInvariant locator roots workspace capacity budget := by
  have pendingZero : pendingDegree workspace.stack roots.pending.val = 0 := by
    simp only [pendingDegree, empty, show (0#usize).val = 0 from rfl, Finset.range_zero, Finset.sum_empty]
  have fits : roots.stride.val ≤ budget + 1 := by
    unfold factorDegreeMass at mass
    omega
  have live : liveDegree roots workspace.stack < roots.stride.val := by
    simp only [liveDegree, pendingZero, Nat.add_zero, stride, Nat.lt_succ_self]
  refine ⟨buffers, degreeBudget, layout, represented, mass, fits, live, fun _ => empty, ?_, ?_⟩
  · intro positive
    have nonzero : roots.degree ≠ 0#usize := by
      intro zero
      rw [zero] at positive
      exact Nat.not_lt_zero 0 positive
    rw [active nonzero]
    exact residualValid
  · intro slot live
    rw [empty] at live
    exact (Nat.not_lt_zero slot live).elim

theorem budget_buffers_same_lengths (before after : RowWorkspace) (capacity budget : Nat)
    (sized : BudgetBuffers before capacity budget)
    (widths : workspaceLengths after = workspaceLengths before) : BudgetBuffers after capacity budget := by
  have bm : after.bm.length = before.bm.length := congrArg WorkspaceAdmission.Lengths.bm widths
  have poly : after.polynomials.length = before.polynomials.length := congrArg WorkspaceAdmission.Lengths.polynomials widths
  have factors : after.factors.length = before.factors.length := congrArg WorkspaceAdmission.Lengths.factors widths
  have table : after.square_table.length = before.square_table.length := congrArg WorkspaceAdmission.Lengths.squareTable widths
  have raw : after.raw.length = before.raw.length := congrArg WorkspaceAdmission.Lengths.raw widths
  have roots : after.roots.length = before.roots.length := congrArg WorkspaceAdmission.Lengths.roots widths
  have stack : after.stack.length = before.stack.length := congrArg WorkspaceAdmission.Lengths.stack widths
  exact ⟨by rw [bm]; exact sized.bm, by rw [poly]; exact sized.polynomials,
    by rw [factors]; exact sized.factors, by rw [table]; exact sized.squareTable,
    by rw [raw]; exact sized.raw, by rw [roots]; exact sized.roots, by rw [stack]; exact sized.stack⟩

#print axioms traversal_invariant_at_start

end BulksketchBridge.RootRun
