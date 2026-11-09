import BulksketchBridge.CandidateMergePassMath

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std
open bulksketch.sketch.candidates bulksketch.sketch.shape

/-- Every fixed-width run in the scratch prefix is ordered by the source
lexicographic bucket and word key, including a final short run. -/
def RunsOrdered (buckets width : Nat) (words : List U64) : Prop :=
  ∀ run, ((words.drop (run * width)).take width).Pairwise
    (fun a b => bucketKey buckets a ≤ bucketKey buckets b)

private theorem capped_run (words : List U64) (width start : Nat) :
    words.slice start (mergeMiddle width words.length start) = (words.drop start).take width := by
  unfold List.slice mergeMiddle
  rw [Nat.add_sub_cancel_left]
  by_cases fits : width ≤ words.length - start
  · rw [Nat.min_eq_left fits]
  · rw [Nat.min_eq_right (by omega)]
    rw [List.take_of_length_le (by rw [List.length_drop]), List.take_of_length_le (by rw [List.length_drop]; omega)]

private theorem merged_run_sorted (buckets width : Nat) (ids : Slice U64) (run : Nat)
    (ordered : RunsOrdered buckets width ids.val) (start : Nat) (alignment : start = run * width) :
    (mergeSelection buckets ids (mergeMiddle width ids.length start) (mergeEnd width ids.length start)
      start (mergeMiddle width ids.length start)).Pairwise
      (fun a b => bucketKey buckets a ≤ bucketKey buckets b) := by
  let middle := mergeMiddle width ids.length start
  apply merge_selection_sorted
  · rw [show ids.val.slice start middle = (ids.val.drop start).take width from capped_run _ _ _,
      alignment]
    exact ordered run
  · rw [show ids.val.slice middle (mergeEnd width ids.length start) =
        (ids.val.drop middle).take width from capped_run _ _ _]
    by_cases complete : start + width ≤ ids.length
    · have middleEq : middle = (run + 1) * width := by
        unfold middle
        rw [merge_middle_eq _ _ _ (by omega), Nat.min_eq_left complete, alignment, Nat.add_mul, Nat.one_mul]
      rw [middleEq]
      exact ordered (run + 1)
    · by_cases inside : start ≤ ids.length
      · have midLast : middle = ids.length := by
          unfold middle
          rw [merge_middle_eq _ _ _ inside, Nat.min_eq_right (by omega)]
        rw [midLast, List.drop_eq_nil_of_le (show ids.val.length ≤ ids.length from le_rfl)]
        simp
      · have midPast : ids.val.length ≤ middle := by
          unfold middle mergeMiddle
          change ids.length ≤ _
          omega
        rw [List.drop_eq_nil_of_le midPast]
        simp

theorem merge_output_runs (buckets width : Nat) (ids : Slice U64) (fuel start run : Nat)
    (positive : 0 < width) (ordered : RunsOrdered buckets width ids.val)
    (alignment : start = run * width) (room : start ≤ ids.length) :
    RunsOrdered buckets (2 * width) (mergeOutput buckets width ids.length ids fuel start) := by
  induction fuel generalizing start run with
  | zero =>
    intro run
    simp [mergeOutput]
  | succ fuel ih =>
    by_cases active : start < ids.length
    · let middle := mergeMiddle width ids.length start
      let stop := mergeEnd width ids.length start
      let block := mergeSelection buckets ids middle stop start middle
      let rest := mergeOutput buckets width ids.length ids fuel stop
      have midEq := merge_middle_eq width ids.length start room
      have stopEq : stop = min (start + 2 * width) ids.length := merge_end_eq width ids.length start room
      have blockLen : block.length = stop - start := by
        apply merge_selection_length _ _ _ _ _ <;> omega
      have blockSorted := merged_run_sorted buckets width ids run ordered start alignment
      have joined : mergeOutput buckets width ids.length ids (fuel + 1) start = block ++ rest := by
        simp only [mergeOutput, active, ite_true, block, rest, middle, stop]
      rw [joined]
      by_cases full : start + 2 * width ≤ ids.length
      · have endExact : stop = start + 2 * width := by rw [stopEq, Nat.min_eq_left full]
        have stopAligned : stop = (run + 2) * width := by rw [endExact, alignment, Nat.add_mul]
        have fullLength : block.length = 2 * width := by rw [blockLen, endExact]; omega
        have next := ih stop (run + 2) stopAligned (by omega)
        intro j
        cases j with
        | zero =>
          rw [Nat.zero_mul, List.drop_zero, ← fullLength, List.take_left]
          exact blockSorted
        | succ j =>
          have position : (j + 1) * (2 * width) = 2 * width + j * (2 * width) := by
            rw [Nat.succ_mul, Nat.add_comm]
          have front : (block ++ rest).drop (2 * width) = rest := by rw [← fullLength, List.drop_left]
          rw [position, ← List.drop_drop, front]
          exact next j
      · have endExact : stop = ids.length := by rw [stopEq, Nat.min_eq_right (by omega)]
        have empty : rest = [] := by unfold rest; rw [endExact, merge_output_end]
        rw [empty, List.append_nil]
        have blockShort : block.length ≤ 2 * width := by rw [blockLen, endExact]; omega
        intro j
        cases j with
        | zero =>
          rw [Nat.zero_mul, List.drop_zero, List.take_of_length_le blockShort]
          exact blockSorted
        | succ j =>
          rw [List.drop_eq_nil_of_le (by rw [Nat.succ_mul]; omega)]
          simp
    · have atEnd : start = ids.length := by omega
      rw [atEnd, merge_output_end]
      intro j
      simp

/-- A complete original merge pass preserves the input permutation and
doubles the width of every ordered run. -/
def ActualNativeMergePassOrder : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (count width : Usize) (ids temporary : Slice U64),
    0 < shape.capacities.length → 0 < width.val →
    count.val = ids.length → temporary.length = ids.length →
    RunsOrdered shape.capacities.length width.val ids.val →
    ∃ merged,
      normalize_loop0_loop0 field shape count ids temporary width 0#usize = .ok merged ∧
      merged.length = ids.length ∧ merged.val.Perm ids.val ∧
      RunsOrdered shape.capacities.length (2 * width.val) merged.val

theorem native_merge_pass_order : ActualNativeMergePassOrder := by
  intro F field shape count width ids temporary positive widthPositive countVal temporaryLen ordered
  have zero : (0#usize).val = 0 := Usize.ofNatCore_val_eq _
  have ran := native_merge_pass field shape count width 0#usize ids temporary ids.length positive
    widthPositive (by rw [zero]; exact Nat.zero_le _) countVal.le
    (by rw [temporaryLen, countVal]) (by rw [zero, Nat.sub_zero, countVal])
  let merged := mergePassFrom shape.capacities.length width.val ids.length ids ids.length 0 temporary
  have mergeCall : normalize_loop0_loop0 field shape count ids temporary width 0#usize = .ok merged := by
    rwa [zero, countVal] at ran
  have layout := merge_pass_layout shape.capacities.length width.val ids.length ids ids.length 0 temporary
    widthPositive (Nat.zero_le _) le_rfl (by rw [temporaryLen]) (by omega)
  have wrote : merged.val = mergeOutput shape.capacities.length width.val ids.length ids ids.length 0 := by
    have full : temporary.val.length ≤ ids.length := temporaryLen.le
    simpa only [merged, List.take_zero, List.nil_append, List.drop_eq_nil_of_le full, List.append_nil] using layout
  refine ⟨merged, mergeCall, (merge_pass_length ..).trans temporaryLen, ?_, ?_⟩
  · rw [wrote]
    have source := merge_output_perm shape.capacities.length width.val ids.length ids ids.length 0
      widthPositive (Nat.zero_le _) (by omega)
    simpa only [List.slice, List.drop_zero, Nat.sub_zero, Slice.length, List.take_length] using source
  · rw [wrote]
    exact merge_output_runs _ _ ids _ _ 0 widthPositive ordered (by simp) (Nat.zero_le _)

#print axioms native_merge_pass_order

end BulksketchBridge.CandidateNormalization
