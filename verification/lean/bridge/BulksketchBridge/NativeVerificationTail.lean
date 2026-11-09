import BulksketchBridge.NativeVerificationDriver

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime ExecutionFinish
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)

def CanonicalizationReady {K : Type} (before : RootDrainState K) : Prop :=
  before.execution.state = .Running .Canonicalization ∧ before.execution.degree_probe = none ∧
  (before.execution.roots.count ≤ before.execution.budget.nonzero →
    before.execution.roots.count.val ≤ before.workspace.roots.length)

def VerificationTailReady {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) (before : RootDrainState K) : Prop :=
  (∃ seed continued,
    before.execution.state = .Running .Verification ∧ before.execution.degree_probe = none ∧
    ExecutionVerify.Bounds kernels before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued ∧
    ∀ (after : RootDrainState K) (reply : core.result.Result RowProgress DecodeError)
      (back : RowWorkspace → RowWorkspace),
      after.execution.state = .Running .Canonicalization →
      nativeCandidateDriver nativeCanonicalize kernels before.execution input before.workspace before.meter =
        .ok (reply, after.execution, after.workspace, back, after.meter) →
      CanonicalizationReady after)
  ∨ CanonicalizationReady before

theorem native_verification_tail_law {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) :
    RankedDriverLaw (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
      (VerificationTailReady kernels input) rootTailRank := by
  intro before _ admitted _
  rcases admitted with ⟨seed, continued, running, noProbe, bounds, canonical⟩ | ⟨running, noProbe, room⟩
  · exact native_verification_ranked_step nativeCanonicalize kernels before input seed continued _
      running noProbe bounds (fun after reply back state ran => Or.inr (canonical after reply back state ran))
  · exact native_canonicalization_ranked_step kernels before input _ running noProbe room

/-- The exact native verifier and canonicalizer supply the final drain
without a separately provided abstract execution trace. -/
def ActualNativeVerificationTailFinish : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) (before : RootDrainState K),
    VerificationTailReady kernels input before →
    ∃ steps ≤ 3, ∃ last : Exit bulksketch.field.Gf64 K,
      DrainTrace (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
        steps before.execution before.workspace before.meter last ∧
      stageOption last.execution.state = none ∧
      finish RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels
        before.execution input before.workspace before.meter = modeled last

theorem native_verification_tail_finish : ActualNativeVerificationTailFinish := by
  intro K kernels input before ready
  obtain ⟨steps, bounded, last, callbacks, trace, terminal, _, _, _, returned⟩ :=
    ranked_native_finish (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
      (VerificationTailReady kernels input) rootTailRank before (native_verification_tail_law kernels input) ready
  have rank : rootTailRank before ≤ 2 := by
    unfold rootTailRank
    rcases ready with ⟨_, _, running, _⟩ | ⟨running, _⟩
    · rw [running]
    · rw [running]
      change 1 ≤ 2
      decide
  exact ⟨steps, by omega, last, trace, terminal, returned⟩

#print axioms native_verification_tail_finish

end BulksketchBridge.ExecutionDriver
