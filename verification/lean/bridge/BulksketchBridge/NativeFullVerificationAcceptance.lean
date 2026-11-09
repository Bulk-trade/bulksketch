import BulksketchBridge.NativeVerificationDriver
import BulksketchBridge.DegreeProbeRuntimeEncoding
import BulksketchBridge.RebuiltLocatorPolynomial

namespace BulksketchBridge.ProbeVerification

open Aeneas.Std Algebra.Gf64 DegreeProbeRuntime DenseCoefficient RebuiltLfsr Reconciliation

private theorem foldColumn_oddSyndrome (roots : Slice U64) (distinct : roots.val.Nodup) (slot : Nat) :
    toField (PortableEncoding.foldColumn roots.val slot 0#u64).bv =
      oddSyndrome (rootSupport roots) slot := by
  classical
  have injective : Function.Injective (fun word : U64 => toField word.bv) :=
    fun left right equal => U64.bv_eq_imp_eq left right (toField_injective equal)
  rw [PortableEncoding.foldColumn_field]
  simp only [show (0#u64).bv = 0 from rfl, toField_zero, zero_add, oddSyndrome, powerSum, rootSupport]
  rw [List.sum_toFinset _ (distinct.map injective), List.map_map]
  rfl

theorem expected_accepts_odd_syndromes (odd roots scratch : Slice U64)
    (distinct : roots.val.Nodup) (bounds : Bounds odd roots scratch) :
    (expected odd roots scratch).1 = true ↔
      ∀ i < odd.length, toField odd[i]!.bv = oddSyndrome (rootSupport roots) i := by
  have wordOfMatch (agreement : ∀ i < odd.length, toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)
      (i : Nat) (inside : i < odd.length) : PortableEncoding.foldColumn roots.val i 0#u64 = odd[i]! :=
    U64.bv_eq_imp_eq _ _ (toField_injective ((foldColumn_oddSyndrome roots distinct i).trans (agreement i inside).symm))
  have passes (agreement : ∀ i < odd.length, toField odd[i]!.bv = oddSyndrome (rootSupport roots) i) :
      precheckRejects odd roots = false := by
    by_cases small : roots.length ≤ 2
    · have first := wordOfMatch agreement 0 (bounds.firstRead small)
      by_cases two : 2 ≤ odd.length
      · have second := wordOfMatch agreement 1 (by omega)
        simp [precheckRejects, small, two, first, second]
      · simp [precheckRejects, small, two, first]
    · simp [precheckRejects, small]
  unfold expected
  split <;> rename_i rejected
  · constructor
    · intro bad
      cases bad
    · intro agreement
      rw [passes agreement] at rejected
      cases rejected
  · have pass : precheckRejects odd roots = false := Bool.eq_false_of_not_eq_true rejected
    have room := bounds.encodingWindow pass
    let shape := prefixSlice scratch odd.length
    have shapeLength : shape.length = odd.length := by
      rw [show shape = prefixSlice scratch odd.length from rfl, prefix_length, Nat.min_eq_left room]
    have wordLength : (encodedWords shape roots).length = odd.length :=
      (encodedWords_length shape roots).trans shapeLength
    have fieldWord (i : Nat) (inside : i < odd.length) :
        toField (encodedWords shape roots)[i]!.bv = oddSyndrome (rootSupport roots) i := by
      rw [encodedWords_slot shape roots i (by rwa [shapeLength])]
      exact foldColumn_oddSyndrome roots distinct i
    change decide (encodedWords shape roots = odd) = true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · intro same i inside
      rw [← same]
      exact fieldWord i inside
    · intro agreement
      apply Slice.ext_getElem wordLength
      intro i outBound inputBound
      rw [Slice.Inhabited_getElem_eq_getElem! _ _ outBound, Slice.Inhabited_getElem_eq_getElem! _ _ inputBound]
      exact U64.bv_eq_imp_eq _ _ (toField_injective ((fieldWord i inputBound).trans (agreement i inputBound).symm))

end BulksketchBridge.ProbeVerification

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 ExecutionDriverRuntime DegreeProbeRuntime RebuiltLfsr Reconciliation
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types

/-- The full encoding branch checks all original odd words, including
the original short-root rejection before the scratch write. -/
def ActualNativeFullVerificationAccepts : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    (∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y) →
    squaringLaw kernels → CorrectEncoding kernels →
    ∀ (before : RootDrainState K) (input : RowInput) (paid : WorkMeter),
      before.execution.state = .Running .Verification → before.execution.degree_probe = none →
      ExecutionVerify.selects before.execution input = false →
      StageCharge.chargeResult before.meter (ExecutionVerify.actualCost before.execution input) = (.Ok (), paid) →
      before.execution.roots.count.val ≤ before.workspace.roots.length →
      let roots := ExecutionVerify.selectedRoots before.execution before.workspace
      roots.val.Nodup → ProbeVerification.Bounds input.difference roots before.workspace.verification →
      let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
        (ExecutionVerify.actualCost before.execution input) before.workspace.verification false
      let after := transition .Verification lower
      nativeCandidateDriver canonicalize kernels before.execution input before.workspace before.meter = .ok after ∧
      (after.2.1.state = .Running .Canonicalization ↔ ∀ i < input.difference.length,
        toField input.difference[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem native_full_verification_accepts : ActualNativeFullVerificationAccepts := by
  intro canonicalize K kernels mul square encoding before input paid running noProbe selected charged rootRoom
    roots distinct bounds
  have admitted : ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) before.workspace.verification false := by
    refine ⟨fun _ => rootRoom, ?_, fun _ _ => ⟨mul, square, encoding, bounds⟩⟩
    intro _ rebuilt
    rw [selected] at rebuilt
    cases rebuilt
  refine ⟨native_verification_driver canonicalize kernels before input _ _ running noProbe admitted, ?_⟩
  have meaning := ProbeVerification.expected_accepts_odd_syndromes input.difference roots
    before.workspace.verification distinct bounds
  simp only [ExecutionVerify.expected, charged, selected, Bool.false_eq_true, ite_false]
  change (transition .Verification _).2.1.state = .Running .Canonicalization ↔
    ∀ i < input.difference.length, toField input.difference[i]!.bv = oddSyndrome (rootSupport roots) i
  rw [← meaning]
  change _ ↔ (ProbeVerification.expected input.difference
    (ExecutionVerify.selectedRoots before.execution before.workspace) before.workspace.verification).1 = true
  cases ProbeVerification.expected input.difference
    (ExecutionVerify.selectedRoots before.execution before.workspace) before.workspace.verification with
  | mk accepted verification => cases accepted <;> simp [transition]

#print axioms native_full_verification_accepts

end BulksketchBridge.ExecutionDriver
