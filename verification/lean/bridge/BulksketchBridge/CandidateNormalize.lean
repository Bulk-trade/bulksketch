import BulksketchBridge.CandidateMergeSort
import BulksketchBridge.CandidateHistogram
import BulksketchBridge.CandidateCompactMeaning
import BulksketchBridge.CandidateRow

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.sketch.candidates bulksketch.sketch.shape

def PackedCandidateRows (packed inputs : Slice U64) (buckets : Nat) : Prop :=
  ∃ used,
    used ≤ inputs.length ∧
    (packed.val.take used).Nodup ∧
    (∀ word, word ∈ packed.val.take used ↔ word ∈ inputs.val ∧ word ≠ 0#u64) ∧
    ∀ bucket : Usize, bucket.val < buckets →
      ∃ hints, row packed inputs.len bucket = .ok hints ∧ hints.val.Nodup ∧
        ∀ word ∈ hints.val, word ≠ 0#u64

/-- The original shared-request normalizer fills the admitted storage and
supplies a distinct, nonzero candidate slice to every actual row accessor. -/
def ActualNativeCandidateNormalize : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F) (inputs storage : Slice U64),
    0 < shape.capacities.length →
    2 * inputs.length + shape.capacities.length + 1 ≤ storage.length →
    ∃ packed,
      normalize field shape inputs storage = .ok packed ∧ packed.length = storage.length ∧
      PackedCandidateRows packed inputs shape.capacities.length

private theorem zero_val_at (words : Slice U64) (index : Nat) (inside : index < (zeroWords words).length) :
    (zeroWords words)[index]!.val = 0 := by
  have insideList : index < (List.replicate words.length (0#u64)).length := by
    simpa only [List.length_replicate, zero_length] using inside
  simp only [zeroWords, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ _ insideList, List.getElem_replicate]
  rfl

private theorem zero_histogram (offsets ids : Slice U64) (room : 0 < offsets.length) :
    HistogramMass ⟨zeroWords offsets, ids, 0⟩ := by
  refine ⟨?_, zero_val_at offsets 0 (by rwa [zero_length])⟩
  simp only [countMass, zeroWords, Slice.from_val, List.map_replicate, List.sum_replicate,
    show (0#u64).val = 0 from rfl, nsmul_zero]

private theorem split_values (whole : Slice U64) (split : Nat) (left right : Slice U64)
    (fits : split ≤ whole.length) (leftLen : left.length = split)
    (rightLen : right.length = whole.length - split) :
    (splitBack whole split (left, right)).val = left.val ++ right.val := by
  unfold splitBack
  rw [dite_eq_left ⟨leftLen.trans (Nat.min_eq_left fits).symm, rightLen⟩]
  simp only [Slice.from_val]

private theorem packed_rows_of_layout (packed inputs ids temporary counts cumulative : Slice U64)
    (buckets used : Nat) (positive : 0 < inputs.length)
    (idLen : ids.length = inputs.length) (temporaryLen : temporary.length = inputs.length)
    (layout : packed.val = ids.val ++ temporary.val ++ cumulative.val)
    (room : buckets < counts.length)
    (bounds : OffsetInvariant counts cumulative buckets)
    (mass : countMass counts = used) (usedRoom : used ≤ inputs.length)
    (distinct : (ids.val.take used).Nodup)
    (support : ∀ word, word ∈ ids.val.take used ↔ word ∈ inputs.val ∧ word ≠ 0#u64) :
    PackedCandidateRows packed inputs buckets := by
  have prefixEq : packed.val.take used = ids.val.take used := by
    rw [layout, List.append_assoc, List.take_append_of_le_length (by change used ≤ ids.length; omega)]
  have rawZero : inputs.len ≠ 0#usize := by
    intro zero
    have zeroLength := congrArg UScalar.val zero
    rw [Slice.len_val, show (0#usize).val = 0 from Usize.ofNatCore_val_eq _] at zeroLength
    omega
  have exactOffsets : CandidateNormalization.offsets packed inputs.len = cumulative := by
    apply Slice.ext
    simp only [CandidateNormalization.offsets, Slice.len_val, tail, Slice.from_val, layout]
    have front : (ids.val ++ temporary.val).length = 2 * inputs.length := by
      simp only [List.length_append]
      change ids.length + temporary.length = _
      omega
    rw [← front, List.drop_left]
  refine ⟨used, usedRoom, prefixEq ▸ distinct, ?_, ?_⟩
  · intro word
    rw [prefixEq]
    exact support word
  · intro bucket selected
    have offsetsRoom : bucket.val + 1 < cumulative.length := by rw [bounds.1]; omega
    have exactStart : rowStart packed inputs.len bucket = offsetAt counts bucket.val := by
      unfold rowStart
      rw [exactOffsets, bounds.2 _ (by omega), ite_eq_left selected.le]
    have exactEnd : rowEnd packed inputs.len bucket = offsetAt counts (bucket.val + 1) := by
      unfold rowEnd
      rw [exactOffsets, bounds.2 _ (by omega), ite_eq_left (by omega : bucket.val + 1 ≤ buckets)]
    have endUsed : rowEnd packed inputs.len bucket ≤ used := by
      rw [exactEnd, ← mass]
      exact offset_bounded _ _
    have packedRoom : 2 * inputs.length ≤ packed.length := by
      have packedLength : packed.length = ids.length + temporary.length + cumulative.length := by
        change packed.val.length = _
        rw [layout, List.length_append, List.length_append]
      omega
    have rowBounds : RowBounds packed inputs.len bucket := by
      intro _
      refine ⟨by rw [Slice.len_val]; exact packedRoom, by rwa [exactOffsets], ?_, by omega⟩
      rw [exactStart, exactEnd]
      exact offset_mono _ (Nat.le_succ _)
    have packedDistinct : (prefixSlice packed used).val.Nodup := by
      simpa only [prefixSlice, Slice.from_val, prefixEq] using distinct
    have packedNonzero : ∀ word ∈ (prefixSlice packed used).val, word ≠ 0#u64 := by
      intro word member
      have inside : word ∈ ids.val.take used := by
        simpa only [prefixSlice, Slice.from_val, prefixEq] using member
      exact ((support word).mp inside).2
    exact native_candidate_row_from_packed packed inputs.len bucket used rowBounds (fun _ => endUsed)
      packedDistinct packedNonzero

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3500000 in
theorem native_candidate_normalize : ActualNativeCandidateNormalize := by
  intro F field shape inputs storage positive admitted
  by_cases empty : inputs.length = 0
  · let packed := zeroWords storage
    have isEmpty : core.slice.Slice.is_empty inputs = .ok true := by
      simp only [core.slice.Slice.is_empty, empty, decide_true]
    refine ⟨packed, ?_, zero_length _, 0, Nat.zero_le _, by simp, ?_, ?_⟩
    · simp only [bulksketch.sketch.candidates.normalize, isEmpty, bind_ok, ite_true, fill_zero, packed]
    · intro word
      have noInput : inputs.val = [] := List.length_eq_zero_iff.mp empty
      simp only [List.take_zero, List.not_mem_nil, noInput, false_and]
    · intro bucket _
      have raw : inputs.len = 0#usize := UScalar.eq_of_val_eq
        ((Slice.len_val inputs).trans (empty.trans (Usize.ofNatCore_val_eq _).symm))
      refine ⟨prefixSlice packed 0, ?_, by simp [prefixSlice], ?_⟩
      · have r := native_candidate_row packed inputs.len bucket (fun h => (h raw).elim)
        simpa [rowView, raw] using r
      · simp [prefixSlice]
  · have storageMax : storage.length ≤ Usize.max := storage.length_ineq
    let size := inputs.len
    have sizeVal : size.val = inputs.length := Slice.len_val _
    have two : (2#usize).val = 2 := Usize.ofNatCore_val_eq _
    obtain ⟨double, doubled, doubleVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := 2#usize) (y := size) (by rw [two, sizeVal]; omega))
    rw [two, sizeVal] at doubleVal
    let arrays := prefixSlice storage (2 * inputs.length)
    let counts := tail storage (2 * inputs.length)
    let temporary := tail arrays inputs.length
    let initialIds := prefixSlice arrays inputs.length
    have arraysLen : arrays.length = 2 * inputs.length := by
      unfold arrays
      rw [prefix_length, Nat.min_eq_left (by omega)]
    have countsLen : counts.length = storage.length - 2 * inputs.length := tail_length _ _
    have temporaryLen : temporary.length = inputs.length := by
      unfold temporary
      rw [tail_length, arraysLen]
      omega
    have initialIdsLen : initialIds.length = inputs.length := by
      unfold initialIds
      rw [prefix_length, Nat.min_eq_left (by omega)]
    have split := split_refines storage double (by rw [doubleVal]; omega)
    rw [doubleVal] at split
    have splitArrays := split_refines arrays size (by rw [sizeVal]; omega)
    rw [sizeVal] at splitArrays
    have copied := ClosedLeaf.copy_normal initialIds inputs initialIdsLen
    let swapOrigin : MergeRestore := fun a b => (a, b)
    have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
    obtain ⟨sorted, scratch, flipped, sortBack, sortedCall, sortedLen, scratchLen, permutation,
      ordered, restore⟩ := native_merge_sort field shape size 1#usize inputs temporary false swapOrigin
        positive (by rw [one]; decide) sizeVal temporaryLen (by rw [one]; exact one_word_runs _ _)
    let finalTemporary := if flipped then sorted else scratch
    let fixBack : MergeRestore := fun a b => if flipped then (b, a) else (a, b)
    have tmpLen : finalTemporary.length = inputs.length := by
      unfold finalTemporary
      split <;> assumption
    have tidy : (if flipped then (do
        let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU64 scratch sorted
        .ok ((DenseGcdRuntime.swapSlots sorted copied).1,
          (DenseGcdRuntime.swapSlots sorted copied).2.1,
          fun a b => (DenseGcdRuntime.swapSlots sorted copied).2.2 (a, b))) else .ok (sorted, scratch, fun a b => (a, b)) :
        Result (Slice U64 × Slice U64 × MergeRestore)) = .ok (sorted, finalTemporary, fixBack) := by
      have copiedSorted := ClosedLeaf.copy_normal scratch sorted (scratchLen.trans sortedLen.symm)
      cases flipped <;> simp only [Bool.false_eq_true, ite_false, ite_true, copiedSorted, bind_ok,
        DenseGcdRuntime.swapSlots, finalTemporary, fixBack] <;> rfl
    let zeroCounts := zeroWords counts
    let initial : CompactState := ⟨zeroCounts, sorted, 0⟩
    let compacted := compactFrom shape.capacities.length inputs.length 0 initial
    let compactCursor : core.ops.range.Range Usize := ⟨0#usize, size⟩
    have zero : (0#usize).val = 0 := Usize.ofNatCore_val_eq _
    have countRoom : shape.capacities.length + 1 ≤ zeroCounts.length := by
      rw [zero_length, countsLen]
      omega
    have initialMass : HistogramMass initial := zero_histogram counts sorted (by omega)
    have initialBounds : CompactBounds shape.capacities.length 0 initial := by
      refine ⟨positive, countRoom, le_rfl, Nat.zero_le _, ?_⟩
      intro slot inside
      change zeroCounts[slot]!.val ≤ 0
      rw [zero_val_at counts slot inside]
    have rawCompact := (native_candidate_compact field shape compactCursor zeroCounts sorted 0#usize
      (by change (0#usize).val ≤ size.val; rw [zero]; exact Nat.zero_le _)
      (by change size.val ≤ sorted.length; rw [sizeVal, sortedLen])
      (by change CompactBounds shape.capacities.length (0#usize).val ⟨zeroCounts, sorted, (0#usize).val⟩;
          simpa only [zero] using initialBounds)).1
    have compactCall : normalize_loop1 field compactCursor shape zeroCounts sorted 0#usize =
        .ok (compacted.offsets, compacted.ids) := by
      have cStart : compactCursor.start.val = 0 := zero
      have cEnd : compactCursor.end.val = inputs.length := sizeVal
      rw [cStart, cEnd, Nat.sub_zero] at rawCompact
      exact rawCompact
    obtain ⟨histogram, compactedLen, countLen⟩ :=
      compact_histogram shape.capacities.length inputs.length 0 initial (by change 0 + inputs.length ≤ sorted.length; omega)
        initialBounds initialMass
    have initialWords : CompactContents sorted 0 initial := ⟨rfl, le_rfl, rfl, by intros; rfl⟩
    have compactContents := compact_loop_contents shape.capacities.length inputs.length 0 sorted initial
      (by rw [sortedLen]; omega) initialWords
    have usedRoom : compacted.used ≤ inputs.length := by
      simpa only [Nat.zero_add] using compactContents.2.1
    have allSorted : sorted.val.take inputs.length = sorted.val :=
      List.take_of_length_le (show sorted.length ≤ inputs.length from sortedLen.le)
    have retained : compacted.ids.val.take compacted.used = compactedWords sorted.val := by
      simpa only [compactedWords, Nat.zero_add, allSorted] using compactContents.2.2.1
    let bucketCount := shape.capacities.len
    let sumCursor : core.ops.range.Range Usize := ⟨0#usize, bucketCount⟩
    have offsetsFit : sumCursor.end.val < compacted.offsets.length := by
      change bucketCount.val < compacted.offsets.length
      rw [Slice.len_val]
      have len : compacted.offsets.length = zeroCounts.length := countLen
      omega
    have histogramMass : countMass compacted.offsets = compacted.used := histogram.1
    have totalFit : countMass compacted.offsets ≤ U64.max := by
      rw [histogramMass]
      apply usedRoom.trans
      have h := usize_fits_u64 size
      rw [sizeVal] at h
      rw [U64.max_eq]
      omega
    obtain ⟨cumulative, offsetCall, summed⟩ := native_candidate_offsets compacted.offsets compacted.offsets
      sumCursor (by change (0#usize).val ≤ bucketCount.val; rw [zero]; exact Nat.zero_le _)
      offsetsFit totalFit (by
        change OffsetInvariant compacted.offsets compacted.offsets (0#usize).val
        rw [zero]
        exact offsets_initial _)
    have restored : sortBack (fixBack compacted.ids finalTemporary).1 (fixBack compacted.ids finalTemporary).2 =
        (compacted.ids, finalTemporary) := by
      rw [restore]
      cases flipped <;> rfl
    let restoredArrays := splitBack arrays inputs.length (compacted.ids, finalTemporary)
    let packed := splitBack storage (2 * inputs.length) (restoredArrays, cumulative)
    have arraysRestoreLen : restoredArrays.length = arrays.length := splitBack_length _ _ _
    have physical : packed.length = storage.length := splitBack_length _ _ _
    have rawLayout : packed.val = compacted.ids.val ++ finalTemporary.val ++ cumulative.val := by
      rw [show packed.val = restoredArrays.val ++ cumulative.val from split_values storage _ _ _
        (by omega) (arraysRestoreLen.trans arraysLen)
        (by rw [summed.1, countLen, zero_length, countsLen])]
      rw [show restoredArrays.val = compacted.ids.val ++ finalTemporary.val from split_values arrays _ _ _
        (by omega) (compactedLen.trans sortedLen) (by rw [tmpLen, arraysLen]; omega)]
    have completeRows : PackedCandidateRows packed inputs shape.capacities.length := by
      apply packed_rows_of_layout packed inputs compacted.ids finalTemporary compacted.offsets cumulative
        shape.capacities.length compacted.used (by omega) (compactedLen.trans sortedLen) tmpLen rawLayout
      · simpa only [sumCursor, bucketCount, Slice.len_val] using offsetsFit
      · simpa only [sumCursor, bucketCount, Slice.len_val] using summed
      · exact histogramMass
      · exact usedRoom
      · rw [retained]; exact compacted_words_distinct _ (bucket_key_injective _) _ ordered
      · intro word
        rw [retained, compacted_words_mem, permutation.mem_iff]
    refine ⟨packed, ?_, physical, completeRows⟩
    have isEmpty : core.slice.Slice.is_empty inputs = .ok false := by
      simp only [core.slice.Slice.is_empty, empty, decide_false]
    rw [bulksketch.sketch.candidates.normalize, isEmpty, bind_ok]
    simp only [Bool.false_eq_true, ite_false]
    rw [show (2#usize * inputs.len : Result Usize) = .ok double from doubled, bind_ok, split, bind_ok]
    dsimp! only
    rw [show core.slice.Slice.split_at_mut (prefixSlice storage (2 * inputs.length)) inputs.len =
      .ok ((initialIds, temporary), splitBack arrays inputs.length) from splitArrays, bind_ok]
    dsimp! only
    rw [copied, bind_ok]
    rw [show normalize_loop0 field (fun a b => (a,b)) shape inputs.len inputs temporary 1#usize false =
      .ok (sorted, scratch, flipped, sortBack) from sortedCall, bind_ok]
    dsimp! only
    rw [tidy, bind_ok]
    dsimp! only
    rw [show core.slice.Slice.fill core.clone.CloneU64 (tail storage (2 * inputs.length)) 0#u64 =
      .ok zeroCounts from fill_zero counts, bind_ok]
    rw [show normalize_loop1 field ⟨0#usize, inputs.len⟩ shape zeroCounts sorted 0#usize =
      .ok (compacted.offsets, compacted.ids) from compactCall, bind_ok]
    dsimp! only
    simp only [SketchShape.bucket_count, bind_ok]
    rw [show normalize_loop2 ⟨0#usize, shape.capacities.len⟩ compacted.offsets = .ok cumulative from offsetCall,
      bind_ok]
    rw [restored]

#print axioms native_candidate_normalize

end BulksketchBridge.CandidateNormalization
