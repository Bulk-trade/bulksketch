import BulksketchBridge.ExecutionVerifyPrice
import BulksketchBridge.RankedRootDrainAdapter

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

#print axioms native_verification_driver

end BulksketchBridge.ExecutionDriver
