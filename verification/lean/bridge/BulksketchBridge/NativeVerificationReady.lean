import BulksketchBridge.NativeVerificationTail

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types

private theorem verification_success_frame {K : Type} (before : RootDrainState K)
    (input : RowInput) (seed : Slice U64) (continued : Bool) :
    let cost := ExecutionVerify.actualCost before.execution input
    let lower := ExecutionVerify.expected before.execution input before.workspace before.meter cost seed continued
    let after := transition .Verification lower
    after.2.1.state = .Running .Canonicalization →
    (StageCharge.chargeResult before.meter cost).1 = .Ok () ∧
    after.2.1.roots = before.execution.roots ∧ after.2.1.degree_probe = before.execution.degree_probe ∧
    after.2.2.1.roots = before.workspace.roots := by
  dsimp only
  unfold transition ExecutionVerify.expected
  cases payment : StageCharge.chargeResult before.meter
      (ExecutionVerify.actualCost before.execution input) with
  | mk reply finalMeter =>
    cases reply with
    | Err error => simp
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
      cases valid <;> simp

/-- Successful native verification preserves precisely the roots and
probe state needed for canonicalization's native slice admission. -/
theorem native_verification_tail_ready {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) (before : RootDrainState K) (seed : Slice U64) (continued : Bool)
    (running : before.execution.state = .Running .Verification)
    (noProbe : before.execution.degree_probe = none)
    (bounds : ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued) :
    VerificationTailReady kernels input before := by
  refine Or.inl ⟨seed, continued, running, noProbe, bounds, ?_⟩
  intro after reply back destination ran
  have model := native_verification_driver nativeCanonicalize kernels before input seed continued
    running noProbe bounds
  let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
    (ExecutionVerify.actualCost before.execution input) seed continued
  let output := transition .Verification lower
  have returned : output = (reply, after.execution, after.workspace, back, after.meter) :=
    Result.ok_injective (model.symm.trans ran)
  have exactExecution : output.2.1 = after.execution :=
    congrArg (fun frame : RunFrame bulksketch.field.Gf64 K => frame.2.1) returned
  have exactWorkspace : output.2.2.1 = after.workspace :=
    congrArg (fun frame : RunFrame bulksketch.field.Gf64 K => frame.2.2.1) returned
  obtain ⟨paid, rootCount, probe, rootWords⟩ := verification_success_frame before input seed continued
    (by change output.2.1.state = _; rwa [exactExecution])
  rw [show (transition .Verification lower).2.1 = after.execution from exactExecution] at rootCount probe
  rw [show (transition .Verification lower).2.2.1 = after.workspace from exactWorkspace] at rootWords
  refine ⟨destination, probe.trans noProbe, fun _ => ?_⟩
  rw [rootCount, rootWords]
  obtain ⟨rootRoom, _, _⟩ := bounds
  exact rootRoom paid

/-- From native verification admission, the original verifier and
canonicalizer construct the terminal finish trace and preserve its exact result. -/
def ActualNativeVerificationStartFinish : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) (before : RootDrainState K) (seed : Slice U64) (continued : Bool),
    before.execution.state = .Running .Verification → before.execution.degree_probe = none →
    ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued →
    ∃ steps ≤ 3, ∃ last : ExecutionFinish.Exit bulksketch.field.Gf64 K,
      ExecutionFinish.DrainTrace (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
        steps before.execution before.workspace before.meter last ∧
      stageOption last.execution.state = none ∧
      Execution.Insts.BulksketchDecodeRowRowExecution.finish
        RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels
        before.execution input before.workspace before.meter = ExecutionFinish.modeled last

theorem native_verification_start_finish : ActualNativeVerificationStartFinish := by
  intro K kernels input before seed continued running noProbe bounds
  exact native_verification_tail_finish kernels input before
    (native_verification_tail_ready kernels input before seed continued running noProbe bounds)

#print axioms native_verification_start_finish

end BulksketchBridge.ExecutionDriver
