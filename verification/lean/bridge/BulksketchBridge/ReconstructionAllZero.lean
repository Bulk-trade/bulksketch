import Arithmetic.ReconstructionGenerated
import Arithmetic.ReconstructionRuntime

namespace BulksketchBridge.Reconstruction

open Aeneas Aeneas.Std Aeneas.Std.ReconstructionRuntime
open bulksketch.decode.stages.Execution

def allZero (words : Slice U64) : Bool :=
  words.val.all (· == 0#u64)

private theorem scan_zero {C : Type} (call : C → U64 → Result (Bool × C))
    (exactCall : ∀ c word, call c word = .ok (word == 0#u64, c))
    (values : List U64) (closure : C) :
    ∃ count, scan call values closure = .ok (values.all (· == 0#u64), count) := by
  induction values with
  | nil => exact ⟨0, rfl⟩
  | cons word values ih =>
    cases h : (word == 0#u64) with
    | false => exact ⟨1, by simp [scan, exactCall, h]⟩
    | true =>
      obtain ⟨count, remaining⟩ := ih
      exact ⟨count + 1, by simp [scan, exactCall, h, remaining]⟩

theorem all_zero_normal {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : bulksketch.backend.contract.BulkKernels K F) (words : Slice U64) :
    ∃ iter, sliceAll (reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool field kernels)
        ⟨words, 0⟩ () = .ok (allZero words, iter) := by
  let dictionary := reconstruct.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool field kernels
  have exactCall : ∀ c word, dictionary.call_mut c word = .ok (word == 0#u64, c) := by
    intro c word
    cases c
    change Result.ok (decide (word = 0#u64), ()) = Result.ok (word == 0#u64, ())
    by_cases h : word = 0#u64 <;> simp [h]
  obtain ⟨count, normal⟩ := scan_zero dictionary.call_mut exactCall words.val ()
  refine ⟨⟨words, count⟩, ?_⟩
  change sliceAll dictionary ⟨words, 0⟩ () = _
  simp [sliceAll, List.drop_zero, normal, allZero]

theorem all_zero_iff (words : Slice U64) :
    allZero words = true ↔ ∀ word ∈ words.val, word = 0#u64 := by
  simp [allZero, List.all_eq_true]

end BulksketchBridge.Reconstruction
