import BulksketchBridge.NativeCandidateDeflateDriver

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next)

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

def rootStage : Stage → Bool
  | .ReducerPreparation | .AffinePreparation | .AffineEnumeration | .AffineSplit
  | .Trace | .Gcd | .FactorDivision | .Leaf | .LeafThree | .LeafFour | .FactorVerification => true
  | _ => false

/-- The original execution and row-driver frames lift an actual root stage
    without altering its lower return, borrow continuation or meter. -/
def ActualNativeRootDriverReturn : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (stage : Stage) (input : RowInput)
    (workspace : RowWorkspace) (meter paid : WorkMeter) (reply : RootReply) (after : Roots)
    (written : RowWorkspace) (back : RowWorkspace → RowWorkspace),
    self.state = .Running stage → self.degree_probe = none → rootStage stage = true →
    Roots.run RootRun.nativeCalls RootRun.nativeDivRem RootSetup.gf64Dictionary kernels self.roots
      stage workspace meter = .ok (reply, after, written, back, paid) →
    nativeCandidateDriver canonicalize kernels self input workspace meter =
      .ok (transition stage (liftRootReply reply, { self with roots := after }, written, back, paid))

theorem native_root_driver_return : ActualNativeRootDriverReturn := by
  intro canonicalize K kernels self stage input workspace meter paid reply after written back
    state noProbe admitted ran
  apply run_next_return RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels self stage input workspace meter _ state
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels self stage input workspace meter]
  unfold expectedExecute
  rw [noProbe]
  cases stage <;> simp only [rootStage, Bool.false_eq_true] at admitted
  all_goals
    dsimp only
    rw [ran, bind_ok]
    rfl

#print axioms native_root_driver_return

end BulksketchBridge.ExecutionDriver
