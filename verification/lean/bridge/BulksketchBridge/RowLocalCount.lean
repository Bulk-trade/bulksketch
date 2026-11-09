import Arithmetic.RowLocalGenerated
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.sketch.candidates
open CandidateRowsRuntime

abbrev DecodeRow := bulksketch.sketch.input.DecodeRow

def rawRowCount {F : Type} (rows : List (DecodeRow F)) : Nat :=
  (rows.map (fun row => row.candidates.length)).sum

private abbrev callback {F : Type} (field : bulksketch.field.BinaryField F) :=
  normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize field

private abbrev mappedRows {F : Type} (field : bulksketch.field.BinaryField F) :=
  mapIterator (core.iter.traits.iterator.IteratorSliceIter (DecodeRow F)) (callback field)

private theorem count_loop {F : Type} (field : bulksketch.field.BinaryField F)
    (rows : Slice (DecodeRow F)) (remaining : List (DecodeRow F)) (position : Nat) (count : Usize)
    (suffix : rows.val.drop position = remaining)
    (fits : count.val + rawRowCount remaining ≤ Usize.max) :
    ∃ result,
      loop (sumBody (mappedRows field)) (⟨⟨rows, position⟩, ()⟩, count) = .ok result ∧
      result.val = count.val + rawRowCount remaining := by
  induction remaining generalizing position count with
  | nil =>
    have exhausted : ¬position < rows.length := by
      have length := congrArg List.length suffix
      simp only [List.length_drop, List.length_nil] at length
      change rows.length - position = 0 at length
      omega
    have nextNone : core.slice.iter.IteratorSliceIter.next ⟨rows, position⟩ =
        .ok (none, ⟨rows, position⟩) := by
      have room : ¬ position < rows.len.val := by rwa [Slice.len_val]
      simp only [core.slice.iter.IteratorSliceIter.next, room, _root_.dite_false]
    refine ⟨count, ?_, by simp [rawRowCount]⟩
    have done : sumBody (mappedRows field) (⟨⟨rows, position⟩, ()⟩, count) = .ok (.done count) := by
      have mapped : mapNext (core.iter.traits.iterator.IteratorSliceIter (DecodeRow F))
          (callback field) ⟨⟨rows, position⟩, ()⟩ =
            .ok (none, ⟨⟨rows, position⟩, ()⟩) := by
        simp only [mapNext, nextNone, bind_ok]
        rfl
      simp only [sumBody, mappedRows, mapIterator, mapped, bind_ok]
      rfl
    rw [loop, done, bind_ok]
  | cons row rest ih =>
    have active : position < rows.val.length := by
      have length := congrArg List.length suffix
      simp only [List.length_drop, List.length_cons] at length
      omega
    have head : rows.val[position] = row := by
      rw [List.drop_eq_getElem_cons active] at suffix
      exact (List.cons.inj suffix).1
    have tail : rows.val.drop (position + 1) = rest := by
      rw [List.drop_eq_getElem_cons active] at suffix
      exact (List.cons.inj suffix).2
    have next : core.slice.iter.IteratorSliceIter.next ⟨rows, position⟩ =
        .ok (some row, ⟨rows, position + 1⟩) := by
      have room : position < rows.len.val := by rwa [Slice.len_val]
      unfold core.slice.iter.IteratorSliceIter.next
      rw [dite_eq_left room]
      exact congrArg (fun element => Result.ok (some element, (⟨rows, position + 1⟩ : core.slice.iter.Iter (DecodeRow F)))) head
    have widthVal : row.candidates.len.val = row.candidates.length := Slice.len_val _
    have remainingCount : rawRowCount (row :: rest) = row.candidates.length + rawRowCount rest := rfl
    obtain ⟨advanced, addition, value⟩ := RawMulTable.normal_of_spec _ _
      (Usize.add_spec (x := count) (y := row.candidates.len) (by rw [widthVal]; omega))
    rw [widthVal] at value
    have step : sumBody (mappedRows field) (⟨⟨rows, position⟩, ()⟩, count) =
        .ok (.cont (⟨⟨rows, position + 1⟩, ()⟩, advanced)) := by
      have mapped : mapNext (core.iter.traits.iterator.IteratorSliceIter (DecodeRow F))
          (callback field) ⟨⟨rows, position⟩, ()⟩ =
            .ok (some row.candidates.len, ⟨⟨rows, position + 1⟩, ()⟩) := by
        simp only [mapNext, next, bind_ok,
          normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize.call_mut]
        rfl
      simp only [sumBody, mappedRows, mapIterator, mapped, bind_ok]
      dsimp! only
      rw [addition, bind_ok]
    obtain ⟨result, normal, total⟩ := ih (position + 1) advanced tail (by omega)
    refine ⟨result, ?_, by omega⟩
    rw [loop, step, bind_ok]
    exact normal

/-- Exact original callback, map iterator and checked sum count. -/
theorem row_local_count {F : Type} (field : bulksketch.field.BinaryField F) (rows : Slice (DecodeRow F))
    (fits : rawRowCount rows.val ≤ Usize.max) :
    ∃ count,
      (do
        let i ← core.slice.Slice.iter rows
        let m ← mapNew (core.iter.traits.iterator.IteratorSliceIter (DecodeRow F)) (callback field) i ()
        sumUsize (mappedRows field) () m : Result Usize) = .ok count ∧ count.val = rawRowCount rows.val := by
  have zero : (0#usize).val = 0 := Usize.ofNatCore_val_eq _
  obtain ⟨count, call, value⟩ := count_loop field rows rows.val 0 0#usize (List.drop_zero)
    (by rw [zero, Nat.zero_add]; exact fits)
  refine ⟨count, ?_, ?_⟩
  · simp only [core.slice.Slice.iter, mapNew, sumUsize, bind_ok]
    exact call
  · simpa only [zero, Nat.zero_add] using value

#print axioms row_local_count

end BulksketchBridge.CandidateNormalization
