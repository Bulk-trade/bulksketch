import Arithmetic.DispatchCompletedGenerated
import BulksketchBridge.NativeCompletedResult

namespace BulksketchBridge.RowDispatch

open Aeneas Aeneas.Std Result
open DenseCoefficient RebuiltLfsr CompletedResult
open bulksketch.decode.probe bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.sketch.dispatch bulksketch.types

def expectedCompleted {F : Type} (before : DecodeExecution F) (workspace : RowWorkspace) :
    Result (core.result.Result RowResult DecodeError) :=
  match before with
  | .Probe probe _ => if probe.next.isNone then decoded workspace probe.count else .fail .assertionFailure
  | .Portable row => outcome row workspace
  | .Pclmul row => outcome row workspace
  | .Vpclmul512 row => outcome row workspace

/-- The native dispatch preserves each row's terminal contract. A drained
tiny probe returns the bounded original workspace roots prefix, with its
original panic paths for a live probe or out-of-range count. -/
def ActualDispatchCompletedResult : Prop :=
  ∀ (d : RowDispatchRuntime.Dictionaries) {F : Type} (field : bulksketch.field.BinaryField F)
    (before : DecodeExecution F) (workspace : RowWorkspace),
    DecodeExecution.completed_result d field before workspace = expectedCompleted before workspace

theorem dispatch_completed_result : ActualDispatchCompletedResult := by
  intro d F field before workspace
  cases before with
  | Portable row => exact native_completed_result field (d.portable field) row workspace
  | Pclmul row => exact native_completed_result field (d.pclmul field) row workspace
  | Vpclmul512 row => exact native_completed_result field (d.vpclmul512 field) row workspace
  | Probe probe backend =>
    simp only [DecodeExecution.completed_result, expectedCompleted,
      Probe.next_stage, Probe.impl.count, bind_ok]
    cases active : probe.next with
    | some stage =>
      simp [core.option.Option.is_none, massert, bind_fail]
    | none =>
      simp only [core.option.Option.is_none, Option.isNone_none, ite_true, massert, bind_ok]
      by_cases bounded : probe.count.val ≤ workspace.roots.length
      · rw [decoded, ite_eq_left bounded, Slice.index_SliceIndexRangeToUsizeSliceInst,
          shared_prefix_normal workspace.roots probe.count bounded, bind_ok]
      · have runtimeBound : ¬ probe.count ≤ workspace.roots.length := bounded
        rw [decoded, ite_eq_right bounded, Slice.index_SliceIndexRangeToUsizeSliceInst,
          core.slice.index.SliceIndexRangeToUsizeSlice.index, ite_eq_right runtimeBound, bind_fail]

#print axioms dispatch_completed_result

end BulksketchBridge.RowDispatch
