import BulksketchBridge.AffineEnumerationBatch

namespace BulksketchBridge.AffineEnumerate

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

private theorem scan_keeps_suffix (degree : Nat) (pairs : List (U64 × U64))
    (roots : Slice U64) (found : Nat) (bounded : found ≤ degree) :
    (scan degree pairs roots found).2.1.val.drop degree = roots.val.drop degree := by
  induction pairs generalizing roots found with
  | nil => rfl
  | cons pair rest ih =>
    obtain ⟨point, value⟩ := pair
    unfold scan
    split
    · exact ih roots found bounded
    split
    · rfl
    split
    · rfl
    · have inside : found < degree := by omega
      rw [ih (roots.setAtNat found point) (found + 1) (by omega)]
      simpa only [Slice.setAtNat, Slice.from_val] using
        (List.drop_set_of_lt (a := point) (l := roots.val) inside)

private theorem batches_keep_suffix {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (rejoin : Slice U64 × Slice U64 → Slice U64)
    (polynomial basis : Slice U64) (degree batch stop start : Nat) (roots points values : Slice U64)
    (point : U64) (found : Nat) (pointRoom : batch ≤ points.length) (valueRoom : batch ≤ values.length)
    (bounded : found ≤ degree) (reply : core.result.Result Usize DecodeFailure) (output scratch : Slice U64)
    (ran : enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
      .ok (reply, output, scratch)) :
    output.val.drop degree = roots.val.drop degree := by
  suffices ∀ fuel start found (roots points values : Slice U64) (point : U64),
      stop - start = fuel → batch ≤ points.length → batch ≤ values.length → found ≤ degree →
      enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
        .ok (reply, output, scratch) → output.val.drop degree = roots.val.drop degree
    from this _ start found roots points values point rfl pointRoom valueRoom bounded ran
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro start found roots points values point remaining pointsRoom valuesRoom foundRoom normal
    by_cases active : start < stop ∧ 0 < batch
    · let width := min batch (stop - start)
      let filled := grayFill basis start (prefixSlice points width) 0 point width
      let valuePrefix := prefixSlice values width
      have pointLen : filled.2.length = width := by
        have restored := (gray_fill_words basis (prefixSlice points width) start 0 point width
          (by rw [prefix_length, Nat.min_eq_left (by omega)]; omega)).2.1
        rw [restored, prefix_length, Nat.min_eq_left (by omega)]
      have valueLen : valuePrefix.length = width := by
        change (prefixSlice values width).length = width
        rw [prefix_length, Nat.min_eq_left (by omega)]
      obtain ⟨evaluated, evaluatedNormal, _, _⟩ := horner polynomial filled.2 valuePrefix
        (pointLen.trans valueLen.symm)
      have keeps := scan_keeps_suffix degree (List.zip filled.2.val evaluated.val) roots found foundRoom
      have nextBound := (scan_frame degree (List.zip filled.2.val evaluated.val) roots found foundRoom).2.2
      rcases scanned : scan degree (List.zip filled.2.val evaluated.val) roots found with ⟨failure, written, next⟩
      rw [scanned] at keeps nextBound
      rw [enumerateBatches, dite_eq_left active] at normal
      change (do
        let evaluated ← kernels.horner_many polynomial filled.2 valuePrefix
        let (failure, written, next) := scan degree (List.zip filled.2.val evaluated.val) roots found
        match failure with
        | some reason =>
          .ok (core.result.Result.Err reason, written, rejoin (restorePrefix points filled.2, restorePrefix values evaluated))
        | none =>
          enumerateBatches kernels rejoin polynomial basis degree batch stop (start + width) written
            (restorePrefix points filled.2) (restorePrefix values evaluated) filled.1 next : Result BatchResult) = _ at normal
      simp only [evaluatedNormal, bind_ok, scanned] at normal
      cases failure with
      | some reason =>
        exact (congrArg (fun frame : BatchResult => frame.2.1.val.drop degree)
          (Result.ok_injective normal).symm).trans keeps
      | none =>
        have widthPositive : 0 < width := Nat.lt_min.mpr ⟨active.2, by omega⟩
        exact (ih (stop - (start + width)) (by omega) (start + width) next written
          (restorePrefix points filled.2) (restorePrefix values evaluated) filled.1 rfl
          (by rwa [restore_length]) (by rwa [restore_length]) nextBound normal).trans keeps
    · rw [enumerateBatches, dite_eq_right active] at normal
      exact congrArg (fun frame : BatchResult => frame.2.1.val.drop degree) (Result.ok_injective normal).symm

/-- Every write in the original native enumeration is below the degree
limit, including early decode failures. The caller's unused suffix is kept. -/
theorem native_enumerate_keeps_suffix {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (polynomial : Slice U64) (base : U64)
    (basis roots work : Slice U64) (polyPositive : 0 < polynomial.length)
    (rootsRoom : polynomial.length - 1 ≤ roots.length) (workRoom : 2 ≤ work.length)
    (rankRoom : basis.length < System.Platform.numBits)
    (reply : core.result.Result Usize DecodeFailure) (output scratch : Slice U64)
    (ran : bulksketch.decode.affine.enumerate BmEntry.fieldDictionary kernels polynomial base basis roots work =
      .ok (reply, output, scratch)) :
    output.val.drop (polynomial.length - 1) = roots.val.drop (polynomial.length - 1) := by
  rw [native_enumerate_refines kernels horner polynomial base basis roots work polyPositive rootsRoom
    workRoom rankRoom] at ran
  let half := work.length / 2
  have batchRoom : batchWidth half ≤ half := by
    unfold batchWidth
    split <;> omega
  exact batches_keep_suffix kernels horner (BmEntry.splitBack work half) polynomial basis
    (polynomial.length - 1) (batchWidth half) (2 ^ basis.length) 0 roots (prefixSlice work half)
    (BmEntry.tail work half) base 0
    (by rw [prefix_length, Nat.min_eq_left (by unfold half; omega)]; exact batchRoom)
    (by rw [BmEntry.tail_length]; unfold half at *; omega) (Nat.zero_le _)
    reply output scratch ran

#print axioms native_enumerate_keeps_suffix

end BulksketchBridge.AffineEnumerate
