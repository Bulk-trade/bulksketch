import Arithmetic.CompletedResultGenerated
import BulksketchBridge.RebuiltLocatorLoop

namespace BulksketchBridge.CompletedResult

open Aeneas Aeneas.Std Result DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types

/-- The returned decoded view is exactly the roots prefix. Its range check
panics only when the source asks for a prefix outside the input slice. -/
def decoded (workspace : RowWorkspace) (count : Usize) : Result (core.result.Result RowResult DecodeError) :=
  if count.val ≤ workspace.roots.length then .ok (.Ok (.Decoded (prefixSlice workspace.roots count.val)))
  else .fail .panic

def outcome {F K : Type} (self : Execution F K) (workspace : RowWorkspace) :
    Result (core.result.Result RowResult DecodeError) :=
  match self.state with
  | .Running _ => .fail .panic
  | .Error error => .ok (.Err error)
  | .Failed reason => .ok (.Ok (.Failed reason))
  | .Complete =>
    if self.roots.count = 0#usize ∧ self.budget.total = self.budget.nonzero then .ok (.Ok .Equal)
    else decoded workspace self.roots.count

private theorem decoded_prefix (workspace : RowWorkspace) (count : Usize) :
    (do
      let words ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U64)
        workspace.roots ⟨count⟩
      Result.ok (core.result.Result.Ok (RowResult.Decoded words))) = decoded workspace count := by
  by_cases bounded : count.val ≤ workspace.roots.length
  · rw [decoded, ite_eq_left bounded, Slice.index_SliceIndexRangeToUsizeSliceInst,
      shared_prefix_normal workspace.roots count bounded, bind_ok]
  · have runtimeBound : ¬ count ≤ workspace.roots.length := bounded
    rw [decoded, ite_eq_right bounded, Slice.index_SliceIndexRangeToUsizeSliceInst,
      core.slice.index.SliceIndexRangeToUsizeSlice.index, ite_eq_right runtimeBound, bind_fail]

/-- Exact native terminal result and panic paths for all states and slice
sizes, including the zero-count decoded view when the budget includes zero. -/
def ActualNativeCompletedResult : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Execution F K) (workspace : RowWorkspace),
    Execution.completed_result field kernels self workspace = outcome self workspace

theorem native_completed_result : ActualNativeCompletedResult := by
  intro F K field kernels self workspace
  cases state : self.state with
  | Running stage => simp only [Execution.completed_result, outcome, state]
  | Error reason => simp only [Execution.completed_result, outcome, state]
  | Failed reason => simp only [Execution.completed_result, outcome, state]
  | Complete =>
    simp only [Execution.completed_result, outcome, state]
    by_cases countZero : self.roots.count = 0#usize
    · by_cases same : self.budget.total = self.budget.nonzero
      · simp only [countZero, same, eq_self, true_and, ite_true]
      · simpa only [countZero, same, eq_self, true_and, ite_true, ite_false] using
          decoded_prefix workspace self.roots.count
    · simpa only [countZero, false_and, ite_false] using decoded_prefix workspace self.roots.count

#print axioms native_completed_result

end BulksketchBridge.CompletedResult
