import BulksketchBridge.RootSetup
import BulksketchBridge.RootPendingBudget

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry RootSetup SliceKernels
open bulksketch.decode.roots bulksketch.decode.scratch

theorem root_start_bounds_of_admitted (degree : Usize) (workspace : RowWorkspace)
    (capacity budget : Nat) (degreeBound : degree.val ≤ budget) (budgetCap : budget ≤ capacity)
    (admitted : WorkspaceAdmission.Admitted (workspaceLengths workspace) capacity budget) :
    RootStartBounds degree workspace := by
  have bm : 4 * (capacity + 1) ≤ workspace.bm.length := admitted.2.2.2.2.2.2.2.2.1
  have bmFits := workspace.bm.length_ineq
  change workspace.bm.length ≤ Usize.max at bmFits
  refine ⟨by omega, ?_⟩
  intro nonzero
  have positive : 0 < budget := by
    apply Nat.pos_of_ne_zero
    intro zero
    apply nonzero
    exact UScalar.eq_of_val_eq (by change degree.val = 0; omega)
  have polynomialRoom := (budget_buffers_of_admitted workspace capacity budget positive admitted).polynomials
  exact ⟨by omega, by omega⟩

theorem started_workspace_lengths (degree : Usize) (workspace : RowWorkspace) :
    workspaceLengths (startedWorkspace degree workspace) = workspaceLengths workspace := by
  by_cases zero : degree = 0#usize
  · simp only [workspaceLengths, startedWorkspace, zero, ite_true]
  · simp only [workspaceLengths, startedWorkspace, zero, ite_false, restore_length]

/-- The original start prepares the traversal for an already counted row.
The source-selected affine flag is explicit. Positive budgets have full traversal
storage, including the polynomial room needed by the pending-layout invariant. -/
def ActualRootTraversalStart : Prop :=
  ∀ (roots : Roots) (degree : Usize) (workspace : RowWorkspace) (capacity budget : Nat) (affine : Bool),
    WorkspaceAdmission.Admitted (workspaceLengths workspace) capacity budget →
    budget ≤ capacity →
    roots.pending = 0#usize →
    roots.count.val + degree.val ≤ budget →
    (if roots.v3 then bulksketch.decode.affine.preferred gf64Dictionary degree
      else .ok false) = .ok affine →
    let next := startedRoots roots degree affine
    let written := startedWorkspace degree workspace
    Roots.start roots degree workspace = .ok (ClosedLeafAdvance.stageFor next, next, written, id) ∧
    next.pending = 0#usize ∧ next.count = roots.count ∧ next.degree = degree ∧
    next.stride.val = degree.val + 1 ∧ next.affine_ready = false ∧
    written.basis.directions = none ∧ written.basis.len = 0#u32 ∧
    WorkspaceAdmission.Admitted (workspaceLengths written) capacity budget ∧
    factorDegreeMass next written.stack = roots.count.val + degree.val ∧
    factorDegreeMass next written.stack ≤ budget ∧
    (degree ≠ 0#usize → activeFactor next written =
      slicePolynomial (prefixSlice workspace.bm (degree.val + 1))) ∧
    (0 < budget → BudgetBuffers written capacity budget ∧
      PendingLayout next written.stack written.factors.length written.polynomials.length) ∧
    (2 ≤ degree.val → factorReady next written)

theorem native_root_traversal_start : ActualRootTraversalStart := by
  intro roots degree workspace capacity budget affine admitted budgetCap empty mass choice
  dsimp only
  have degreeBound : degree.val ≤ budget := by omega
  have bounds := root_start_bounds_of_admitted degree workspace capacity budget degreeBound budgetCap admitted
  have admittedWritten : WorkspaceAdmission.Admitted
      (workspaceLengths (startedWorkspace degree workspace)) capacity budget := by
    rwa [started_workspace_lengths]
  have strideVal : (startedRoots roots degree affine).stride.val = degree.val + 1 :=
    ClosedLeafAdvance.word_val _ bounds.1
  have emptyAfter : (startedRoots roots degree affine).pending = 0#usize := empty
  have massExact : factorDegreeMass (startedRoots roots degree affine) (startedWorkspace degree workspace).stack =
      roots.count.val + degree.val := by
    simp only [factorDegreeMass, pendingDegree, startedRoots, startedWorkspace, empty,
      show (0#usize).val = 0 from rfl, Finset.range_zero, Finset.sum_empty, Nat.add_zero]
  refine ⟨?_, emptyAfter, rfl, rfl, strideVal, rfl, rfl, rfl, admittedWritten, massExact,
    massExact ▸ mass, ?_, ?_, ?_⟩
  · rw [root_start_refines roots degree workspace bounds, choice, bind_ok]
  · intro nonzero
    obtain ⟨poly, bm⟩ := bounds.2 nonzero
    have len : (prefixSlice workspace.bm (degree.val + 1)).length = degree.val + 1 := by
      rw [prefix_length, Nat.min_eq_left (by omega)]
    unfold activeFactor
    simp only [startedRoots, startedWorkspace, nonzero, ite_false]
    apply congrArg slicePolynomial
    simpa only [len] using DenseGcd.prefix_restored workspace.polynomials
      (prefixSlice workspace.bm (degree.val + 1)) (by rw [len]; omega)
  · intro positive
    have buffers := budget_buffers_of_admitted (startedWorkspace degree workspace) capacity budget positive admittedWritten
    have poly := buffers.polynomials
    exact ⟨buffers, empty_pending_layout _ _ emptyAfter (by rw [strideVal]; omega)⟩
  · intro minimum
    have positive : 0 < budget := by omega
    have buffers := budget_buffers_of_admitted (startedWorkspace degree workspace) capacity budget positive admittedWritten
    exact (gcd_buffers_of_budget _ _ capacity budget buffers minimum degreeBound).1

#print axioms native_root_traversal_start

end BulksketchBridge.RootRun
