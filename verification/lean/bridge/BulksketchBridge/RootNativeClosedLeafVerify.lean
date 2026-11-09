import BulksketchBridge.ClosedLeafAcceptance
import BulksketchBridge.RootTraversalPotential
import BulksketchBridge.NativeRootRun

namespace BulksketchBridge.ClosedLeaf

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RootRun ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The original paid small-degree certificate either falls back to reducer
preparation or emits the exact certified factor roots and advances. -/
def ActualNativeClosedLeafVerify : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (capacity budget : Nat),
    Cubic.CorrectArithmetic kernels → (roots.degree = 3#usize ∨ roots.degree = 4#usize) →
    roots.solved_count.val ≤ 4 → BudgetBuffers workspace capacity budget →
    factorDegreeMass roots workspace.stack ≤ budget →
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    StageCharge.chargeResult meter (.Ok (leafPrice roots .FactorVerification)) = (.Ok (), paid) →
    let (valid, product) := certificateResult roots workspace
    if valid then
      roots.solved_count.val = roots.degree.val ∧ Certificate.ValidRoots (candidateWords roots workspace) ∧
      slicePolynomial (factorWords roots workspace) =
        ∏ i ∈ Finset.range (candidateWords roots workspace).length,
          (X + C (toField (candidateWords roots workspace)[i]!.bv)) ∧
      ∃ stage after written,
        Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorVerification workspace meter =
          .ok (normalReturn stage after written paid) ∧
        after.count.val = roots.count.val + roots.degree.val ∧
        written.roots = workspace.roots.setSlice! roots.count.val (candidateWords roots workspace).val ∧
        PendingLayout after written.stack written.factors.length written.polynomials.length ∧
        (roots.pending = 0#usize → stage = .Verification) ∧
        (roots.pending ≠ 0#usize → ∃ frame, workspace.stack.val[roots.pending.val - 1]? = some frame ∧
          activeFactor after written = pendingFactor workspace frame ∧
          factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack ∧
          traversalPotential after written.stack < traversalPotential roots workspace.stack)
    else
      Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorVerification workspace meter =
        .ok (normalReturn .ReducerPreparation roots (checkedWorkspace workspace product) paid)

theorem native_closed_leaf_verify : ActualNativeClosedLeafVerify := by
  intro K kernels roots workspace meter paid capacity budget arithmetic degree count sized mass layout charged
  have degreeMin : 3 ≤ roots.degree.val := by rcases degree with h | h <;> rw [h] <;> decide
  have degreeRoom : roots.count.val + roots.degree.val ≤ budget := by unfold factorDegreeMass at mass; omega
  have polyRoom := sized.polynomials
  have rootsRoom := degreeRoom.trans sized.roots
  have admitted : Admitted roots .FactorVerification workspace :=
    ⟨degree, by omega, fun _ => by omega, fun _ => count, fun _ _ => rootsRoom⟩
  have dispatch : Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorVerification workspace meter =
      Roots.closed_leaf fieldDictionary kernels roots .FactorVerification workspace meter :=
    original_root_run_refines kernels roots .FactorVerification workspace meter trivial
  rcases cert : certificateResult roots workspace with ⟨valid, product⟩
  cases valid with
  | false =>
    rw [dispatch, closed_leaf_refines kernels roots .FactorVerification workspace meter arithmetic admitted]
    simp only [expected, charged, verifying, ite_true, verificationFrame, cert, Bool.false_eq_true, ite_false]
    rfl
  | true =>
    have accepted : (certificateResult roots workspace).1 = true := by rw [cert]
    obtain ⟨countExact, validRoots, factorEq⟩ :=
      (certificate_meaning kernels roots workspace arithmetic admitted).mp accepted
    obtain ⟨newCount, newValue, finished, popped⟩ :=
      accepted_advance kernels roots workspace meter paid product arithmetic admitted charged cert
    let counted := { roots with count := newCount }
    let scratch := acceptedWorkspace roots workspace product
    have polyWidth : scratch.polynomials.length = workspace.polynomials.length := by
      simp only [scratch, acceptedWorkspace, checkedWorkspace, Slice.setSlice!_length]
    have scratchLayout : PendingLayout counted scratch.stack scratch.factors.length scratch.polynomials.length := by
      rw [polyWidth]
      exact ⟨layout.stackRoom, layout.factorRoom, layout.polynomialRoom, layout.slots⟩
    refine ⟨countExact, validRoots, factorEq, ?_⟩
    by_cases empty : roots.pending = 0#usize
    · exact ⟨.Verification, counted, scratch, dispatch.trans (finished empty), newValue, rfl,
        scratchLayout, fun _ => rfl, fun impossible => (impossible empty).elim⟩
    · obtain ⟨frame, bounds, _⟩ := pop_bounds_of_pending_layout counted scratch scratchLayout empty
      let after := poppedRoots counted scratch frame
      let written := poppedWorkspace scratch frame
      have exactRun : Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorVerification workspace meter =
          .ok (normalReturn (stageFor after) after written paid) := dispatch.trans (popped frame bounds)
      refine ⟨stageFor after, after, written, exactRun, newValue, rfl,
        popped_pending_layout counted scratch frame scratchLayout, fun impossible => (empty impossible).elim, ?_⟩
      intro _
      have old : PopBounds roots scratch frame := bounds
      have fits : roots.count.val + roots.degree.val ≤ Usize.max := rootsRoom.trans workspace.roots.length_ineq
      have sameCount : newCount = usizeWord (roots.count.val + roots.degree.val) :=
        UScalar.eq_of_val_eq (newValue.trans (word_val _ fits).symm)
      have massEq := popped_degree_mass roots scratch frame old fits
      have decreases := popped_potential_decreases roots scratch frame old (by omega)
      refine ⟨frame, bounds.2.1, popped_factor counted scratch frame bounds, ?_, decreases⟩
      have unchangedStack : scratch.stack = workspace.stack := rfl
      rw [unchangedStack] at massEq
      simpa only [after, written, counted, sameCount] using massEq

#print axioms native_closed_leaf_verify

end BulksketchBridge.ClosedLeaf
