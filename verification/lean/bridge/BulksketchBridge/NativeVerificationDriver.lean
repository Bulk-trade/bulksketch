import BulksketchBridge.ExecutionVerifyPrice
import BulksketchBridge.RankedRootDrainAdapter
import BulksketchBridge.NativeCanonicalizeDriver

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime ExecutionFinish
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096

/-- The original verification driver returns the exact checked verifier
reply, prices and scratch updates, and latches its native destination. -/
def ActualNativeVerificationDriver : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (before : RootDrainState K) (input : RowInput) (seed : Slice U64) (continued : Bool),
    before.execution.state = .Running .Verification → before.execution.degree_probe = none →
    let cost := ExecutionVerify.actualCost before.execution input
    ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter cost seed continued →
    nativeCandidateDriver canonicalize kernels before.execution input before.workspace before.meter =
      .ok (transition .Verification
        (ExecutionVerify.expected before.execution input before.workspace before.meter cost seed continued))

theorem native_verification_driver : ActualNativeVerificationDriver := by
  intro canonicalize K kernels before input seed continued running noProbe cost admitted
  apply run_next_return RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels before.execution .Verification input before.workspace before.meter _ running
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels before.execution .Verification input before.workspace before.meter, expectedExecute, noProbe]
  exact ExecutionVerify.verify_with_prices_refines kernels before.execution input before.workspace
    before.meter seed continued admitted

theorem verification_destination {K : Type} (before : RootDrainState K)
    (input : RowInput) (seed : Slice U64) (continued : Bool) :
    let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued
    let after := (transition .Verification lower).2.1
    stageOption after.state = none ∨ after.state = .Running .Canonicalization := by
  dsimp only
  unfold transition ExecutionVerify.expected
  cases payment : StageCharge.chargeResult before.meter
      (ExecutionVerify.actualCost before.execution input) with
  | mk reply finalMeter =>
    cases reply with
    | Err error => simp [stageOption]
    | Ok charged =>
      cases charged
      dsimp only
      generalize checked : (if ExecutionVerify.selects before.execution input then
        ExecutionVerify.rebuiltExpected (ExecutionVerify.selectedRoots before.execution before.workspace)
          input.difference before.workspace.bm before.workspace.verification seed continued
        else
          let (accepted, updated) := ProbeVerification.expected input.difference
            (ExecutionVerify.selectedRoots before.execution before.workspace) before.workspace.verification
          (accepted, before.workspace.bm, updated)) = output
      obtain ⟨valid, bm, verification⟩ := output
      cases valid <;> simp [stageOption]

theorem native_verification_ranked_step {K : Type} (canonicalize : Canonicalize)
    (kernels : BulkKernels K bulksketch.field.Gf64) (before : RootDrainState K)
    (input : RowInput) (seed : Slice U64) (continued : Bool) (admitted : RootDrainState K → Prop)
    (running : before.execution.state = .Running .Verification)
    (noProbe : before.execution.degree_probe = none)
    (bounds : ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued)
    (canonical : ∀ (after : RootDrainState K) (reply : core.result.Result RowProgress DecodeError)
      (back : RowWorkspace → RowWorkspace), after.execution.state = .Running .Canonicalization →
      nativeCandidateDriver canonicalize kernels before.execution input before.workspace before.meter =
        .ok (reply, after.execution, after.workspace, back, after.meter) →
      admitted after) :
    RankedDriverStep (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
      admitted rootTailRank before := by
  let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
    (ExecutionVerify.actualCost before.execution input) seed continued
  let output := transition .Verification lower
  let after : RootDrainState K := ⟨output.2.1, output.2.2.1, output.2.2.2.2⟩
  have ran := native_verification_driver canonicalize kernels before input seed continued running noProbe bounds
  refine ⟨output.1, after, output.2.2.2.1, ran, ?_⟩
  have next := verification_destination before input seed continued
  change stageOption after.execution.state = none ∨ after.execution.state = .Running .Canonicalization at next
  cases output.1 with
  | Err _ => trivial
  | Ok value =>
    rcases next with terminal | stage
    · exact Or.inl terminal
    · exact Or.inr ⟨canonical after output.1 output.2.2.2.1 stage ran,
        verification_to_canonicalization_rank before after running stage⟩

theorem native_canonicalization_ranked_step {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (before : RootDrainState K)
    (input : RowInput) (admitted : RootDrainState K → Prop)
    (running : before.execution.state = .Running .Canonicalization)
    (noProbe : before.execution.degree_probe = none)
    (room : before.execution.roots.count ≤ before.execution.budget.nonzero →
      before.execution.roots.count.val ≤ before.workspace.roots.length) :
    RankedDriverStep (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
      admitted rootTailRank before := by
  let output := canonicalStageResult before.execution before.workspace before.meter
  let after : RootDrainState K := ⟨output.2.1, output.2.2.1, output.2.2.2.2⟩
  have ran := canonical_stage_refines kernels before.execution input before.workspace before.meter running noProbe room
  refine ⟨output.1, after, output.2.2.2.1, ran, ?_⟩
  have terminal : stageOption after.execution.state = none := by
    unfold after output canonicalStageResult
    cases payment : canonicalStageCharge before.execution before.meter with
    | mk charged meter =>
      cases charged with
      | Err _ => rfl
      | Ok paid =>
        cases paid
        by_cases excess : before.execution.roots.count > before.execution.budget.nonzero
        · simp [stageOption, excess]
        · simp only [excess, ite_false]
          cases bad : CanonicalizeOrdering.invalid gf64Mask
            (Aeneas.Std.DegreeProbeRuntime.sortedWords (selectedCanonicalRoots before.execution before.workspace)).val
          <;> simp [stageOption, bad]

  cases output.1 with
  | Err _ => trivial
  | Ok _ => exact Or.inl terminal

#print axioms native_verification_driver
#print axioms native_verification_ranked_step
#print axioms native_canonicalization_ranked_step

end BulksketchBridge.ExecutionDriver
