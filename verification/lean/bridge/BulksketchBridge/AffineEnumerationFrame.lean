import BulksketchBridge.AffineEnumerationBatch

namespace BulksketchBridge.AffineEnumerate

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem joined_length (work : Slice U64) (half : Nat) (parts : Slice U64 × Slice U64) :
    (splitBack work half parts).length = work.length := by
  unfold splitBack
  split
  · rename_i equal
    simp only [Slice.length, Slice.from_val, List.length_append]
    change parts.1.length + parts.2.length = work.length
    omega
  · rfl

/-- The finite recurrence returns normally on every admitted batch schedule.
Both result branches preserve the lengths of the root and work slices. -/
theorem batches_frame {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (rejoin : Slice U64 × Slice U64 → Slice U64)
    (workLength : Nat) (joined : ∀ parts, (rejoin parts).length = workLength)
    (polynomial basis : Slice U64) (degree batch stop start : Nat) (roots points values : Slice U64)
    (point : U64) (found : Nat) (positive : 0 < batch) (pointRoom : batch ≤ points.length)
    (valueRoom : batch ≤ values.length) (degreeFits : degree ≤ Usize.max) (bounded : found ≤ degree) :
    ∃ reply written work,
      enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
        .ok (reply, written, work) ∧
      written.length = roots.length ∧ work.length = workLength ∧
      ∀ count, reply = .Ok count → count.val = degree := by
  suffices ∀ fuel start found (roots points values : Slice U64) (point : U64),
      stop - start = fuel → batch ≤ points.length → batch ≤ values.length → found ≤ degree →
      ∃ reply written work,
        enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
          .ok (reply, written, work) ∧
        written.length = roots.length ∧ work.length = workLength ∧
        ∀ count, reply = .Ok count → count.val = degree
    from this _ start found roots points values point rfl pointRoom valueRoom bounded
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro start found roots points values point remaining pointsRoom valuesRoom foundRoom
    by_cases active : start < stop
    · let width := min batch (stop - start)
      let pointPrefix := prefixSlice points width
      let valuePrefix := prefixSlice values width
      have pointLength : pointPrefix.length = width := by
        rw [show pointPrefix = prefixSlice points width from rfl, prefix_length, Nat.min_eq_left (by omega)]
      have valueLength : valuePrefix.length = width := by
        rw [show valuePrefix = prefixSlice values width from rfl, prefix_length, Nat.min_eq_left (by omega)]
      let filled := grayFill basis start pointPrefix 0 point width
      have filledWidth : filled.2.length = width :=
        (gray_fill_words basis pointPrefix start 0 point width (by omega)).2.1.trans pointLength
      obtain ⟨evaluated, normal, _, _⟩ := horner polynomial filled.2 valuePrefix (filledWidth.trans valueLength.symm)
      obtain ⟨writtenLength, _, nextBound⟩ :=
        scan_frame degree (List.zip filled.2.val evaluated.val) roots found foundRoom
      rcases scanned : scan degree (List.zip filled.2.val evaluated.val) roots found with ⟨failure, written, nextCount⟩
      rw [scanned] at writtenLength nextBound
      let nextPoints := restorePrefix points filled.2
      let nextValues := restorePrefix values evaluated
      have paid : start < stop ∧ 0 < batch := ⟨active, positive⟩
      have ran :
          enumerateBatches kernels rejoin polynomial basis degree batch stop start roots points values point found =
            match failure with
            | some reason => .ok (.Err reason, written, rejoin (nextPoints, nextValues))
            | none =>
              enumerateBatches kernels rejoin polynomial basis degree batch stop (start + width)
                written nextPoints nextValues filled.1 nextCount := by
        rw [enumerateBatches, dite_eq_left paid]
        change (do
          let out ← kernels.horner_many polynomial filled.2 valuePrefix
          let (failure, written, nextCount) := scan degree (List.zip filled.2.val out.val) roots found
          match failure with
          | some reason => .ok (core.result.Result.Err reason, written, rejoin (nextPoints, restorePrefix values out))
          | none =>
            enumerateBatches kernels rejoin polynomial basis degree batch stop (start + width)
              written nextPoints (restorePrefix values out) filled.1 nextCount) = _
        simp only [normal, Bind.bind, bind_ok, scanned, nextValues]
        cases failure <;> rfl
      cases failure with
      | some reason =>
        exact ⟨.Err reason, written, rejoin (nextPoints, nextValues), ran, writtenLength, joined _, by simp⟩
      | none =>
        have widthPositive : 0 < width := Nat.lt_min.mpr ⟨positive, by omega⟩
        obtain ⟨reply, output, work, rest, outLength, workLen, exactCount⟩ :=
          ih _ (by omega) (start + width) nextCount written nextPoints nextValues filled.1 rfl
            (by simpa only [nextPoints, restore_length] using pointsRoom)
            (by simpa only [nextValues, restore_length] using valuesRoom) nextBound
        exact ⟨reply, output, work, ran.trans rest, outLength.trans writtenLength, workLen, exactCount⟩
    · rw [enumerateBatches, dite_eq_right (fun guard => active guard.1)]
      by_cases exactSize : found = degree
      · refine ⟨.Ok (ClosedLeafAdvance.usizeWord found), roots, rejoin (points, values),
          by simp only [exactSize, ite_true], rfl, joined _, ?_⟩
        intro count equality
        cases equality
        rw [ClosedLeafAdvance.word_val _ (by rwa [exactSize]), exactSize]
      · exact ⟨.Err .NotSplit, roots, rejoin (points, values),
          by simp only [exactSize, ite_false], rfl, joined _, by simp⟩

/-- The original enumerator returns a bounded exact count or its original
error, with both mutable slices restored to their original widths. -/
theorem native_enumeration_frame {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (polynomial : Slice U64) (base : U64) (basis roots work : Slice U64)
    (polyPositive : 0 < polynomial.length) (rootRoom : polynomial.length - 1 ≤ roots.length)
    (workRoom : 2 ≤ work.length) (rank : basis.length < System.Platform.numBits) :
    ∃ reply written scratch,
      bulksketch.decode.affine.enumerate BmEntry.fieldDictionary kernels polynomial base basis roots work =
        .ok (reply, written, scratch) ∧
      written.length = roots.length ∧ scratch.length = work.length ∧
      ∀ count, reply = .Ok count → count.val = polynomial.length - 1 := by
  let half := work.length / 2
  have halfFits : half ≤ work.length := by unfold half; omega
  have halfPositive : 0 < half := by unfold half; omega
  have batchBounds : 0 < batchWidth half ∧ batchWidth half ≤ half := by
    unfold batchWidth
    split <;> omega
  obtain ⟨reply, written, scratch, normal, rootLength, workLength, exactCount⟩ :=
    batches_frame kernels horner (splitBack work half) work.length (joined_length work half)
      polynomial basis (polynomial.length - 1) (batchWidth half) (2 ^ basis.length) 0
      roots (prefixSlice work half) (tail work half) base 0 batchBounds.1
      (by rw [prefix_length, Nat.min_eq_left halfFits]; exact batchBounds.2)
      (by rw [tail_length]; unfold half at *; omega)
      (rootRoom.trans roots.length_ineq) (Nat.zero_le _)
  exact ⟨reply, written, scratch,
    (native_enumerate_refines kernels horner polynomial base basis roots work polyPositive rootRoom workRoom rank).trans normal,
    rootLength, workLength, exactCount⟩

end BulksketchBridge.AffineEnumerate
