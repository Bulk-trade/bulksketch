import BulksketchBridge.CandidateMergeBlock

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std

theorem merge_middle_eq (width count start : Nat) (ordered : start ≤ count) :
    mergeMiddle width count start = min (start + width) count := by
  unfold mergeMiddle
  omega

theorem merge_end_eq (width count start : Nat) (ordered : start ≤ count) :
    mergeEnd width count start = min (start + 2 * width) count := by
  unfold mergeEnd
  dsimp only
  rw [merge_middle_eq _ _ _ ordered]
  omega

def mergeOutput (buckets width count : Nat) (ids : Slice U64) : Nat → Nat → List U64
  | 0, _ => []
  | fuel + 1, start =>
    if start < count then
      let middle := mergeMiddle width count start
      let stop := mergeEnd width count start
      mergeSelection buckets ids middle stop start middle ++ mergeOutput buckets width count ids fuel stop
    else []

@[simp] theorem merge_output_end (buckets width count : Nat) (ids : Slice U64) (fuel : Nat) :
    mergeOutput buckets width count ids fuel count = [] := by
  cases fuel <;> simp [mergeOutput]

theorem merge_selection_length (buckets : Nat) (ids : Slice U64) (start middle stop : Nat)
    (left : start ≤ middle) (right : middle ≤ stop) (bounds : stop ≤ ids.length) :
    (mergeSelection buckets ids middle stop start middle).length = stop - start := by
  have inside : stop ≤ ids.val.length := bounds
  simp only [mergeSelection, List.length_merge, List.slice_length,
    Nat.min_eq_right (Nat.sub_le_sub_right (right.trans inside) start),
    Nat.min_eq_right (Nat.sub_le_sub_right inside middle)]
  omega

private theorem block_write (buckets width count start : Nat) (ids temporary : Slice U64)
    (ordered : start ≤ count) (inputRoom : count ≤ ids.length) (outputRoom : count ≤ temporary.length) :
    let middle := mergeMiddle width count start
    let stop := mergeEnd width count start
    (mergeBlock buckets width count start ids temporary).val =
      temporary.val.take start ++ mergeSelection buckets ids middle stop start middle ++ temporary.val.drop stop := by
  dsimp only
  let middle := mergeMiddle width count start
  let stop := mergeEnd width count start
  let run := mergeSelection buckets ids middle stop start middle
  have midEq := merge_middle_eq width count start ordered
  have stopEq := merge_end_eq width count start ordered
  have runLen : run.length = stop - start := by
    apply merge_selection_length _ _ _ _ _ <;> omega
  have fits : run.length ≤ temporary.val.length - start := by
    change count ≤ temporary.val.length at outputRoom
    omega
  have endAt : start + run.length = stop := by omega
  simp only [mergeBlock, Slice.setSlice!_val]
  change temporary.val.setSlice! start run = temporary.val.take start ++ run ++ temporary.val.drop stop
  simp only [List.setSlice!, Nat.min_eq_left fits, List.take_length, endAt]

private theorem take_and_drop_written (prefixWords merged rest : List U64) (start stop count : Nat)
    (startLength : prefixWords.length = start) (mergedLength : merged.length = stop - start)
    (ordered : start ≤ stop) (finished : stop ≤ count) :
    (prefixWords ++ merged ++ rest).take stop = prefixWords ++ merged ∧
      (prefixWords ++ merged ++ rest).drop count = rest.drop (count - stop) := by
  have length : (prefixWords ++ merged).length = stop := by simp only [List.length_append]; omega
  constructor
  · rw [← length, List.take_left]
  · rw [show count = stop + (count - stop) by omega, ← List.drop_drop, ← length, List.drop_left]
    congr 1
    omega

/-- The whole pass overwrites exactly the consecutive merge runs, and
retains both the prefix before the cursor and the suffix beyond count. -/
theorem merge_pass_layout (buckets width count : Nat) (ids : Slice U64)
    (fuel start : Nat) (temporary : Slice U64)
    (positive : 0 < width) (ordered : start ≤ count)
    (inputRoom : count ≤ ids.length) (outputRoom : count ≤ temporary.length)
    (enough : count - start ≤ fuel) :
    (mergePassFrom buckets width count ids fuel start temporary).val =
      temporary.val.take start ++ mergeOutput buckets width count ids fuel start ++ temporary.val.drop count := by
  induction fuel generalizing start temporary with
  | zero =>
    have endEq : start = count := by omega
    simp only [mergePassFrom, mergeOutput, List.append_nil, endEq, List.take_append_drop]
  | succ fuel ih =>
    by_cases active : start < count
    · let middle := mergeMiddle width count start
      let stop := mergeEnd width count start
      let run := mergeSelection buckets ids middle stop start middle
      let next := mergeBlock buckets width count start ids temporary
      have midEq := merge_middle_eq width count start ordered
      have stopEq := merge_end_eq width count start ordered
      have nextRoom : count ≤ next.length := by
        change count ≤ (mergeBlock buckets width count start ids temporary).length
        rwa [merge_block_length]
      have runLen : run.length = stop - start := by
        apply merge_selection_length _ _ _ _ _ <;> omega
      have originalLen : start ≤ temporary.val.length := ordered.trans outputRoom
      obtain ⟨kept, after⟩ := take_and_drop_written (temporary.val.take start) run
        (temporary.val.drop stop) start stop count (by rw [List.length_take, Nat.min_eq_left originalLen])
        runLen (by omega) (by omega)
      have written : next.val = temporary.val.take start ++ run ++ temporary.val.drop stop :=
        block_write buckets width count start ids temporary ordered inputRoom outputRoom
      have before : next.val.take stop = temporary.val.take start ++ run := by
        rw [written]
        exact kept
      have untouched : next.val.drop count = temporary.val.drop count := by
        rw [written, after, List.drop_drop, Nat.add_sub_of_le (by omega : stop ≤ count)]
      have rest := ih stop next (by omega) nextRoom (by omega)
      simp only [mergePassFrom, mergeOutput, active, ite_true]
      change (mergePassFrom buckets width count ids fuel stop next).val =
        temporary.val.take start ++ (run ++ mergeOutput buckets width count ids fuel stop) ++ temporary.val.drop count
      rw [rest, before, untouched]
      simp only [List.append_assoc]
    · have endEq : start = count := by omega
      simp only [mergePassFrom, mergeOutput, endEq, Nat.lt_irrefl, ite_false, List.append_nil, List.take_append_drop]

private theorem slice_split (words : List U64) (start middle stop : Nat)
    (left : start ≤ middle) (right : middle ≤ stop) :
    words.slice start middle ++ words.slice middle stop = words.slice start stop := by
  have shifted : (words.drop start).drop (middle - start) = words.drop middle := by
    rw [List.drop_drop, Nat.add_sub_of_le left]
  unfold List.slice
  rw [← shifted, ← List.take_add, show middle - start + (stop - middle) = stop - start by omega]

theorem merge_output_perm (buckets width count : Nat) (ids : Slice U64) (fuel start : Nat)
    (positive : 0 < width) (ordered : start ≤ count) (enough : count - start ≤ fuel) :
    (mergeOutput buckets width count ids fuel start).Perm (ids.val.slice start count) := by
  induction fuel generalizing start with
  | zero =>
    have endEq : start = count := by omega
    simp [mergeOutput, endEq, List.slice]
  | succ fuel ih =>
    by_cases active : start < count
    · let middle := mergeMiddle width count start
      let stop := mergeEnd width count start
      have midEq := merge_middle_eq width count start ordered
      have stopEq := merge_end_eq width count start ordered
      have block := merge_selection_perm buckets ids middle stop start middle
      have rest := ih stop (by omega) (by omega)
      have result := block.append rest
      rw [slice_split ids.val start middle stop (by omega) (by omega),
        slice_split ids.val start stop count (by omega) (by omega)] at result
      simpa only [mergeOutput, active, ite_true, middle, stop] using result
    · have endEq : start = count := by omega
      simp [mergeOutput, endEq, List.slice]

#print axioms merge_pass_layout
#print axioms merge_output_perm

end BulksketchBridge.CandidateNormalization
