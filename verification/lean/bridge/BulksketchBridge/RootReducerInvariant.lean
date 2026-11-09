import BulksketchBridge.RootTraversalInvariant
import BulksketchBridge.RootNativeReducerPreparation
import BulksketchBridge.RootTraversalRankLinks

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient
open DenseReducerAlgebra
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096

/-- A paid native reducer step preserves the full represented traversal,
    supplies a correct table at the exact next borrow, and decreases the
    source phase rank without changing the active factor or stack. -/
def ActualNativeReducerInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    TimesXMod.ExactScaleXor kernels →
    bulksketch.decode.roots.charge meter (.Table roots.degree) = .ok (.Ok (), paid) →
    ∃ written,
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .ReducerPreparation workspace meter =
        .ok (.Ok (.Ok (tableStage roots)), roots, written, id, paid) ∧
      RootTraversalInvariant locator roots written capacity budget ∧
      CorrectTable (buffersFor roots written).modulus (buffersFor roots written).table roots.degree.val ∧
      traversalRank (tableStage roots) roots written < traversalRank .ReducerPreparation roots workspace

theorem native_reducer_invariant : ActualNativeReducerInvariant := by
  intro K kernels locator roots workspace meter paid capacity budget invariant minimum scale charged
  obtain ⟨sized, budgeted, layout, represented, exactMass, stride, live, zeroActive, active, pending⟩ := invariant
  have degreeBudget : roots.degree.val ≤ budget := by unfold factorDegreeMass at exactMass; omega
  have positive : 0 < roots.degree.val := by omega
  obtain ⟨monic, exactDegree, _, _, _⟩ := active positive
  let before := buffersFor roots workspace
  have monicWord : before.modulus[roots.degree.val]! = 1#u64 := by
    have width : before.modulus.length = roots.degree.val + 1 :=
      (gcd_buffers_of_budget roots workspace capacity budget sized (by omega) degreeBudget).2.1
    have coefficient : (slicePolynomial before.modulus).coeff roots.degree.val = 1 := by
      change (activeFactor roots workspace).coeff roots.degree.val = 1
      rw [← exactDegree, ← Polynomial.leadingCoeff]
      exact monic
    rw [slicePolynomial_coeff, ite_eq_left (by omega)] at coefficient
    apply U64.bv_eq_imp_eq
    exact toField_injective (coefficient.trans toField_one.symm)
  obtain ⟨table, work, ran, reborrow, correct, widths, activeEq⟩ :=
    native_reducer_preparation kernels roots workspace meter paid capacity budget sized minimum degreeBudget scale charged monicWord
  let updated := { before with table, work }
  let written := rebuild workspace roots updated
  change buffersFor roots written = updated at reborrow
  have polyWidth : written.polynomials.length = workspace.polynomials.length :=
    congrArg WorkspaceAdmission.Lengths.polynomials widths
  have layoutWritten : PendingLayout roots written.stack written.factors.length written.polynomials.length := by
    rw [polyWidth]
    exact layout
  have product : activeTraversalProduct roots written = locator := by
    unfold activeTraversalProduct at represented ⊢
    rw [ite_eq_right (Nat.ne_of_gt positive)] at represented ⊢
    unfold traversalProduct at represented ⊢
    simp only [Bool.false_eq_true, ite_false] at represented ⊢
    unfold liveProduct at represented ⊢
    rw [activeEq]
    exact represented
  refine ⟨written, ran, ?_, ?_, ?_⟩
  · exact ⟨budget_buffers_same_lengths workspace written capacity budget sized widths, budgeted,
      layoutWritten, product, exactMass, stride, live, zeroActive, fun positive => activeEq.symm ▸ active positive, pending⟩
  · rw [reborrow]
    exact correct
  · apply traversal_rank_decreases
    exact Or.inr ⟨rfl, reducer_phase_step roots⟩

#print axioms native_reducer_invariant

end BulksketchBridge.RootRun
