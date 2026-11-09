import BulksketchBridge.CandidateMergeOrder

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.sketch.candidates bulksketch.sketch.shape

abbrev MergeRestore := Slice U64 → Slice U64 → Slice U64 × Slice U64

/-- The original width-doubling loop sorts all keys, preserves every input
occurrence, and returns the exact slot permutation for subsequent writes. -/
def ActualNativeMergeSort : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (count width : Usize) (ids temporary : Slice U64) (flipped : Bool) (back : MergeRestore),
    0 < shape.capacities.length → 0 < width.val →
    count.val = ids.length → temporary.length = ids.length →
    RunsOrdered shape.capacities.length width.val ids.val →
    ∃ (sorted scratch : Slice U64) (finalFlag : Bool) (finalBack : MergeRestore),
      normalize_loop0 field back shape count ids temporary width flipped =
        .ok (sorted, scratch, finalFlag, finalBack) ∧
      sorted.length = ids.length ∧ scratch.length = ids.length ∧
      sorted.val.Perm ids.val ∧
      sorted.val.Pairwise (fun a b => bucketKey shape.capacities.length a ≤ bucketKey shape.capacities.length b) ∧
      ∀ left right, finalBack left right = if finalFlag = flipped then back left right else back right left

private theorem full_run_order (buckets width : Nat) (words : List U64)
    (runs : RunsOrdered buckets width words) (fits : words.length ≤ width) :
    words.Pairwise (fun a b => bucketKey buckets a ≤ bucketKey buckets b) := by
  simpa only [Nat.zero_mul, List.drop_zero, List.take_of_length_le fits] using runs 0

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem native_merge_sort : ActualNativeMergeSort := by
  intro F field shape count width ids temporary flipped back positive widthPositive countEq temporaryEq ordered
  suffices ∀ fuel (width : Usize) (ids temporary : Slice U64) (flipped : Bool) (back : MergeRestore),
    count.val - width.val = fuel → 0 < width.val → count.val = ids.length →
    temporary.length = ids.length → RunsOrdered shape.capacities.length width.val ids.val →
    ∃ (sorted scratch : Slice U64) (finalFlag : Bool) (finalBack : MergeRestore),
      normalize_loop0 field back shape count ids temporary width flipped =
        .ok (sorted, scratch, finalFlag, finalBack) ∧
      sorted.length = ids.length ∧ scratch.length = ids.length ∧ sorted.val.Perm ids.val ∧
      sorted.val.Pairwise (fun a b => bucketKey shape.capacities.length a ≤ bucketKey shape.capacities.length b) ∧
      ∀ left right, finalBack left right = if finalFlag = flipped then back left right else back right left from
    this _ width ids temporary flipped back rfl widthPositive countEq temporaryEq ordered
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro width ids temporary flipped back fuelEq widthPositive countEq temporaryEq ordered
    by_cases active : width.val < count.val
    · obtain ⟨merged, mergedCall, mergedLength, mergedPerm, mergedRuns⟩ :=
        native_merge_pass_order field shape count width ids temporary positive widthPositive countEq temporaryEq ordered
      obtain ⟨remaining, subCall, remainingVal, _⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := count) (y := width) active.le)
      let swapped : MergeRestore := fun left right => back right left
      by_cases finish : count.val - width.val ≤ width.val
      · have doneStep : normalize_loop0.body field shape count back ids temporary width flipped =
            .ok (.done (merged, ids, !flipped, swapped)) := by
          have guard : remaining.val ≤ width.val := by rw [remainingVal]; exact finish
          simp only [normalize_loop0.body, UScalar.lt_equiv, active, ite_true, mergedCall, bind_ok]
          dsimp! only
          simp only [DenseGcdRuntime.swapSlots, subCall, bind_ok, UScalar.le_equiv, guard, ite_true, Prod.swap]
          cases flipped <;> rfl
        have finalOrder : merged.val.Pairwise
            (fun a b => bucketKey shape.capacities.length a ≤ bucketKey shape.capacities.length b) :=
          full_run_order _ _ _ mergedRuns (by change merged.length ≤ _; omega)
        refine ⟨merged, ids, !flipped, swapped, ?_, mergedLength, rfl, mergedPerm, finalOrder, ?_⟩
        · unfold normalize_loop0 loop
          dsimp only
          rw [doneStep, bind_ok]
        · intro left right
          cases flipped <;> rfl
      · have two : (2#usize).val = 2 := Usize.ofNatCore_val_eq _
        have max : ids.length ≤ Usize.max := ids.length_ineq
        have product : width.val * (2#usize).val ≤ Usize.max := by rw [two]; omega
        obtain ⟨double, mulCall, doubleVal⟩ := RawMulTable.normal_of_spec _ _
          (Usize.mul_spec (x := width) (y := 2#usize) product)
        rw [two, Nat.mul_comm] at doubleVal
        have step : normalize_loop0.body field shape count back ids temporary width flipped =
            .ok (.cont (swapped, merged, ids, double, !flipped)) := by
          have guard : ¬ remaining.val ≤ width.val := by rw [remainingVal]; exact finish
          simp only [normalize_loop0.body, UScalar.lt_equiv, active, ite_true, mergedCall, bind_ok]
          dsimp! only
          simp only [DenseGcdRuntime.swapSlots, subCall, bind_ok, UScalar.le_equiv, guard, ite_false, Prod.swap,
            mulCall]
          cases flipped <;> rfl
        have smaller : count.val - double.val < fuel := by rw [doubleVal]; omega
        obtain ⟨sorted, scratch, flag, restored, call, sortedLen, scratchLen, permutation, sortedKeys, frame⟩ :=
          ih (count.val - double.val) smaller double merged ids (!flipped) swapped rfl
            (by rw [doubleVal]; omega) (countEq.trans mergedLength.symm) mergedLength.symm
            (by rwa [doubleVal])
        refine ⟨sorted, scratch, flag, restored, ?_, sortedLen.trans mergedLength, scratchLen.trans mergedLength,
          permutation.trans mergedPerm, sortedKeys, ?_⟩
        · unfold normalize_loop0 loop
          dsimp only
          rw [step, bind_ok]
          exact call
        · intro left right
          rw [frame]
          cases flipped <;> cases flag <;> rfl
    · have step : normalize_loop0.body field shape count back ids temporary width flipped =
          .ok (.done (ids, temporary, flipped, back)) := by
        simp only [normalize_loop0.body, UScalar.lt_equiv, active, ite_false]
      have sorted : ids.val.Pairwise
          (fun a b => bucketKey shape.capacities.length a ≤ bucketKey shape.capacities.length b) :=
        full_run_order _ _ _ ordered (by change ids.length ≤ _; omega)
      refine ⟨ids, temporary, flipped, back, ?_, rfl, temporaryEq, .refl _, sorted, ?_⟩
      · unfold normalize_loop0 loop
        dsimp only
        rw [step, bind_ok]
      · intro left right
        rw [ite_eq_left rfl]

theorem one_word_runs (buckets : Nat) (words : List U64) : RunsOrdered buckets 1 words := by
  intro run
  cases suffix : words.drop (run * 1) with
  | nil => simp
  | cons word tail => simp

#print axioms native_merge_sort

end BulksketchBridge.CandidateNormalization
