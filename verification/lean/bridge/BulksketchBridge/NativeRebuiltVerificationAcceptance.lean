import BulksketchBridge.NativeVerificationDriver
import BulksketchBridge.RebuiltLfsrAnyContinuation

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime Algebra.Gf64 DenseCoefficient RebuiltLfsr Reconciliation
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

def RebuiltSeedLaw {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ shape roots : Slice U64, shape.length ≤ roots.length → roots.val.Nodup →
    ∃ seed : Slice U64, kernels.insert_nonzero (zeroWords shape) roots = .ok seed ∧
      seed.length = shape.length ∧
      ∀ i < seed.length, toField seed[i]!.bv = oddSyndrome (rootSupport roots) i

/-- Exact paid native verification transition when the source selects its
rebuilt branch. Every original odd word participates in acceptance. -/
def ActualNativeRebuiltVerificationAccepts : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    linearLaw kernels → squaringLaw kernels → ContinuationLaw kernels → RebuiltSeedLaw kernels →
    ∀ (before : RootDrainState K) (input : RowInput) (paid : WorkMeter),
      before.execution.state = .Running .Verification → before.execution.degree_probe = none →
      ExecutionVerify.selects before.execution input = true →
      StageCharge.chargeResult before.meter (ExecutionVerify.actualCost before.execution input) = (.Ok (), paid) →
      before.execution.roots.count.val ≤ before.workspace.roots.length →
      let roots := ExecutionVerify.selectedRoots before.execution before.workspace
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < before.workspace.bm.length →
      min roots.length input.difference.length ≤ before.workspace.verification.length →
      ∃ seed continued,
        let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
          (ExecutionVerify.actualCost before.execution input) seed continued
        let after := transition .Verification lower
        nativeCandidateDriver canonicalize kernels before.execution input before.workspace before.meter = .ok after ∧
        (after.2.1.state = .Running .Canonicalization ↔ ∀ i < input.difference.length,
          toField input.difference[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem native_rebuilt_verification_accepts : ActualNativeRebuiltVerificationAccepts := by
  intro canonicalize K kernels linear square recurrence seedLaw before input paid
    running noProbe selected charged rootRoom roots distinct nonzero coefficientsRoom seedRoom
  let odd := input.difference
  let coefficients := before.workspace.bm
  let expected := before.workspace.verification
  let shape := prefixSlice expected (min roots.length odd.length)
  have shapeWidth : shape.length = min roots.length odd.length := by
    unfold shape
    rw [prefix_length, Nat.min_eq_left seedRoom]
  obtain ⟨seed, insert, seedLen, seedMeaning⟩ := seedLaw shape roots (by rw [shapeWidth]; omega) distinct
  have width : seed.length = min roots.length odd.length := seedLen.trans shapeWidth
  have exactInsert : kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots = .ok seed := by
    rw [width]
    exact insert
  let squared := squareFrom (locatorWords roots (prefixSlice coefficients (roots.length + 1))) 1
  have nonempty : 0 < squared.length := by
    have room : roots.length + 1 ≤ coefficients.length := coefficientsRoom
    simp only [squared, square_length, locatorWords, locator_length, Slice.setAtNat_length,
      zero_length, prefix_length, Nat.min_eq_left room]
    omega
  obtain ⟨continued, actualContinue, _⟩ := recurrence odd squared nonempty
  have admitted : ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued := by
    refine ⟨fun _ => rootRoom, fun _ _ => ?_, ?_⟩
    · exact ⟨linear, square, coefficientsRoom, seedRoom, width, exactInsert, fun _ => actualContinue⟩
    · intro _ direct
      rw [selected] at direct
      cases direct
  have exactStage := native_verification_driver canonicalize kernels before input seed continued running noProbe admitted
  obtain ⟨accepted, output, updated, actualRebuild, meaning⟩ :=
    rebuilt_lfsr_any_continuation kernels linear square recurrence roots odd coefficients expected seed
      distinct nonzero coefficientsRoom seedRoom width exactInsert seedMeaning
  obtain ⟨modeledResult, modeledRun, modeledFlag⟩ :=
    rebuilt_lfsr_refines kernels linear square roots odd coefficients expected seed
      coefficientsRoom seedRoom width exactInsert (fun _ => ⟨continued, actualContinue⟩)
  have exactFlag : modeledResult = accepted :=
    congrArg Prod.fst (Result.ok_injective (modeledRun.symm.trans actualRebuild))
  have flag : (ExecutionVerify.rebuiltExpected roots odd coefficients expected seed continued).1 = accepted := by
    change (decide (seed = prefixSlice odd seed.length) && continued) = accepted
    by_cases agrees : seed = prefixSlice odd seed.length
    · rw [ite_eq_left agrees] at modeledFlag
      have same : modeledResult = continued := Result.ok_injective (modeledFlag.symm.trans actualContinue)
      have decision : decide (seed = prefixSlice odd seed.length) = true :=
        decide_eq_true_eq.mpr agrees
      rw [decision, Bool.true_and]
      exact same.symm.trans exactFlag
    · rw [ite_eq_right agrees] at modeledFlag
      have decision : decide (seed = prefixSlice odd seed.length) = false :=
        decide_eq_false_iff_not.mpr agrees
      rw [decision, Bool.false_and]
      exact modeledFlag.symm.trans exactFlag
  refine ⟨seed, continued, exactStage, ?_⟩
  simp only [ExecutionVerify.expected, charged, selected, ite_true]
  generalize model : ExecutionVerify.rebuiltExpected
    (ExecutionVerify.selectedRoots before.execution before.workspace)
      input.difference before.workspace.bm before.workspace.verification seed continued = result
  change (ExecutionVerify.rebuiltExpected
    (ExecutionVerify.selectedRoots before.execution before.workspace)
      input.difference before.workspace.bm before.workspace.verification seed continued).1 = accepted at flag
  rw [model] at flag
  obtain ⟨valid, bm, verification⟩ := result
  change valid = accepted at flag
  rw [← flag] at meaning
  change _ ↔ ∀ i < odd.length, toField odd[i]!.bv = oddSyndrome (rootSupport roots) i
  rw [← meaning]
  cases valid <;> simp [transition]

#print axioms native_rebuilt_verification_accepts

end BulksketchBridge.ExecutionDriver
