import BulksketchBridge.RowLocalOuter
import BulksketchBridge.CandidateRow

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result DenseCoefficient BmEntry RebuiltLfsr
open bulksketch.sketch.candidates

private theorem split_words (whole : Slice U64) (split : Nat) (left right : Slice U64)
    (fits : split ≤ whole.length) (leftLen : left.length = split)
    (rightLen : right.length = whole.length - split) :
    (splitBack whole split (left, right)).val = left.val ++ right.val := by
  unfold splitBack
  rw [dite_eq_left ⟨leftLen.trans (Nat.min_eq_left fits).symm, rightLen⟩]
  simp only [Slice.from_val]

private theorem zero_count_word (buffer : Slice U64) (positive : 0 < buffer.length) :
    (zeroWords buffer)[0]!.val = 0 := by
  have room : 0 < (List.replicate buffer.length (0#u64)).length := by
    rw [List.length_replicate]
    exact positive
  simp only [zeroWords, Slice.from_val, Slice.getElem!_Nat_eq]
  rw [← List.Inhabited_getElem_eq_getElem! _ _ room, List.getElem_replicate]
  rfl

private theorem offset_le_payload (rows : List (Slice U64)) (bucket : Nat) :
    localOffset rows bucket ≤ (localPayload rows).length := by
  have append : localPayload (rows.take bucket) ++ localPayload (rows.drop bucket) = localPayload rows := by
    simp only [localPayload]
    rw [← List.flatMap_append, List.take_append_drop]
  unfold localOffset
  rw [← append, List.length_append]
  exact Nat.le_add_right _ _

/-- The original row-local wrapper returns the exact independently
normalized row for every admitted bucket. Repeats in different rows
remain separate. The only size premise is the admitted physical arena. -/
def ActualNativeRowLocalNormalize : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (rows : Slice (DecodeRow F)) (storage : Slice U64),
    2 * rawRowCount rows.val + rows.length + 1 ≤ storage.length →
    ∃ count packed,
      count.val = rawRowCount rows.val ∧ normalize_rows field rows storage = .ok packed ∧
      packed.length = storage.length ∧
      ∀ (bucket : Usize) (live : bucket.val < rows.length),
        ∃ hints,
          row packed count bucket = .ok hints ∧
          hints.val = normalizedRowWords rows[bucket.val].candidates ∧ hints.val.Nodup ∧
          ∀ word, word ∈ hints.val ↔ word ∈ rows[bucket.val].candidates.val ∧ word ≠ 0#u64

private theorem packed_model {F : Type} (rows : Slice (DecodeRow F)) (count : Usize)
    (packed ids temporary offsets : Slice U64) (used : Nat)
    (positive : count ≠ 0#usize) (countVal : count.val = rawRowCount rows.val)
    (idLen : ids.length = count.val) (temporaryLen : temporary.length = count.val)
    (offsetRoom : rows.length + 1 ≤ offsets.length)
    (layout : packed.val = ids.val ++ temporary.val ++ offsets.val)
    (final : RowLocalPrefix rows rows.length used offsets ids)
    (bucket : Usize) (live : bucket.val < rows.length) :
    ∃ hints, row packed count bucket = .ok hints ∧
      hints.val = normalizedRowWords rows[bucket.val].candidates := by
  obtain ⟨usedVal, usedBound, payload, writtenOffsets⟩ := final
  let sourceRows := rowHints rows.val
  have sourceLen : sourceRows.length = rows.length := by simp [sourceRows, rowHints, Slice.length]
  have all : rows.val.take rows.length = rows.val := List.take_length
  have usedFits : used ≤ count.val := by rw [all, ← countVal] at usedBound; exact usedBound
  have normalized : packed.val.take used = localPayload sourceRows := by
    rw [layout, List.append_assoc, List.take_append_of_le_length (by change used ≤ ids.length; omega), payload]
    simp only [rowPrefixWords, all, sourceRows]
  have usedExact : used = (localPayload sourceRows).length := by
    simpa only [rowPrefixWords, all, sourceRows] using usedVal
  have offsetsExact : CandidateNormalization.offsets packed count = offsets := by
    apply Slice.ext
    simp only [CandidateNormalization.offsets, tail, Slice.from_val, layout]
    have arrays : (ids.val ++ temporary.val).length = 2 * count.val := by
      simp only [List.length_append]
      change ids.length + temporary.length = _
      omega
    rw [← arrays, List.drop_left]
  have offsetEq (k : Nat) : (rowPrefixWords rows k).length = localOffset sourceRows k := by
    simp only [rowPrefixWords, rowHints, localOffset, sourceRows, List.map_take]
  have startExact : rowStart packed count bucket = localOffset sourceRows bucket.val := by
    unfold rowStart
    rw [offsetsExact, writtenOffsets bucket.val live.le, offsetEq]
  have endExact : rowEnd packed count bucket = localOffset sourceRows (bucket.val + 1) := by
    unfold rowEnd
    rw [offsetsExact, writtenOffsets (bucket.val + 1) (by omega), offsetEq]
  have endUsed : rowEnd packed count bucket ≤ used := by
    rw [endExact, usedExact]
    exact offset_le_payload _ _
  have ordered : rowStart packed count bucket ≤ rowEnd packed count bucket := by
    rw [startExact, endExact]
    unfold localOffset localPayload
    rw [List.take_succ_eq_append_getElem (show bucket.val < sourceRows.length by rwa [sourceLen]),
      List.flatMap_append, List.length_append]
    exact Nat.le_add_right _ _
  have length : packed.length = ids.length + temporary.length + offsets.length := by
    change packed.val.length = _
    rw [layout, List.length_append, List.length_append]
  have bounds : RowBounds packed count bucket := by
    intro _
    refine ⟨by omega, by rw [offsetsExact]; omega, ordered, by omega⟩
  refine ⟨rowView packed count bucket, native_candidate_row packed count bucket bounds, ?_⟩
  rw [rowView, ite_eq_right positive, ← ClosedLeaf.region_prefix packed used _ _ endUsed]
  simp only [ClosedLeaf.region, prefixSlice, Slice.from_val, normalized, startExact, endExact]
  have bucketIn : bucket.val < sourceRows.length := by rwa [sourceLen]
  rw [row_local_payload_slice sourceRows bucket.val bucketIn]
  simp only [sourceRows, rowHints, List.getElem_map]
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in
theorem native_row_local_normalize : ActualNativeRowLocalNormalize := by
  intro F field rows storage admitted
  have maximum : storage.length ≤ Usize.max := storage.length_ineq
  have countFits : rawRowCount rows.val ≤ Usize.max := by omega
  obtain ⟨count, total, countVal⟩ := row_local_count field rows countFits
  simp only [core.slice.Slice.iter, CandidateRowsRuntime.mapNew, bind_ok] at total
  by_cases empty : count = 0#usize
  · let packed := zeroWords storage
    have zero : (0#usize).val = 0 := Usize.ofNatCore_val_eq _
    have emptyCount : rawRowCount rows.val = 0 := by rw [← countVal, empty, zero]
    refine ⟨count, packed, countVal, ?_, zero_length _, ?_⟩
    · simp only [normalize_rows, core.slice.Slice.iter, CandidateRowsRuntime.mapNew, bind_ok,
        total, empty, ite_true, fill_zero, packed]
    · intro bucket live
      have rawZero : rows[bucket.val].candidates.length = 0 := by
        apply (List.sum_eq_zero_iff_forall_eq_nat.mp emptyCount)
        exact List.mem_map.mpr ⟨rows[bucket.val], List.getElem_mem (show bucket.val < rows.val.length from live), rfl⟩
      have wordsZero : rows[bucket.val].candidates.val = [] := List.length_eq_zero_iff.mp rawZero
      have normalized : normalizedRowWords rows[bucket.val].candidates = [] := by
        simp only [normalizedRowWords, Aeneas.Std.DegreeProbeRuntime.sortedWords, Slice.from_val, wordsZero,
          List.mergeSort_nil, compactedWords, List.foldl_nil, List.reverse_nil]
      refine ⟨prefixSlice packed 0, ?_, ?_, by simp [prefixSlice], ?_⟩
      · have source := native_candidate_row packed count bucket (fun ne => (ne empty).elim)
        simpa [rowView, empty] using source
      · simp only [prefixSlice, Slice.from_val, List.take_zero, normalized]
      · simp [prefixSlice, wordsZero]
  · have two : (2#usize).val = 2 := Usize.ofNatCore_val_eq _
    obtain ⟨double, doubled, doubleVal⟩ := RawMulTable.normal_of_spec _ _
      (Usize.mul_spec (x := 2#usize) (y := count) (by rw [two, countVal]; omega))
    rw [two] at doubleVal
    let arrays := prefixSlice storage (2 * count.val)
    let offsets := tail storage (2 * count.val)
    let ids := prefixSlice arrays count.val
    let temporary := tail arrays count.val
    have arraysLen : arrays.length = 2 * count.val := by
      unfold arrays
      rw [prefix_length, Nat.min_eq_left (by omega)]
    have offsetLen : offsets.length = storage.length - 2 * count.val := tail_length _ _
    have idsLen : ids.length = count.val := by
      unfold ids
      rw [prefix_length, Nat.min_eq_left (by omega)]
    have tempLen : temporary.length = count.val := by
      unfold temporary
      rw [tail_length, arraysLen]
      omega
    have split := split_refines storage double (by rw [doubleVal]; omega)
    rw [doubleVal] at split
    have splitArrays := split_refines arrays count (by omega)
    let zeroOffsets := zeroWords offsets
    let iter : RowIterator F := ⟨⟨rows,0⟩,0#usize⟩
    have zero : (0#usize).val = 0 := Usize.ofNatCore_val_eq _
    have zeroRoom : rows.length + 1 ≤ zeroOffsets.length := by
      rw [zero_length, offsetLen]
      omega
    have init : RowLocalPrefix rows 0 (0#usize).val zeroOffsets ids := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [rowPrefixWords, zero, List.take_zero, rowHints, List.map_nil, localPayload,
          List.flatMap_nil, List.length_nil]
      · rw [zero]
        exact Nat.zero_le _
      · simp only [rowPrefixWords, zero, List.take_zero, rowHints, List.map_nil, localPayload, List.flatMap_nil]
      · intro slot none
        have equal : slot = 0 := by omega
        subst slot
        rw [zero_count_word offsets (by omega)]
        simp only [rowPrefixWords, List.take_zero, rowHints, List.map_nil, localPayload,
          List.flatMap_nil, List.length_nil]
    obtain ⟨writtenOffsets, writtenIds, used, outer, offsetsLength, idsLength, final⟩ :=
      native_row_local_outer rows 0 0#usize 0#usize zeroOffsets ids
        (Nat.zero_le _) zero zeroRoom (by rw [← countVal, idsLen]) init
    let restoredArrays := splitBack arrays count.val (writtenIds, temporary)
    let packed := splitBack storage (2 * count.val) (restoredArrays, writtenOffsets)
    have layout : packed.val = writtenIds.val ++ temporary.val ++ writtenOffsets.val := by
      have restoredLen : restoredArrays.length = arrays.length := splitBack_length _ _ _
      rw [show packed.val = restoredArrays.val ++ writtenOffsets.val from
        split_words storage _ _ _ (by omega) (restoredLen.trans arraysLen)
          (by rw [offsetsLength, zero_length, offsetLen])]
      rw [show restoredArrays.val = writtenIds.val ++ temporary.val from
        split_words arrays _ _ _ (by omega) (idsLength.trans idsLen) (by rw [tempLen, arraysLen]; omega)]
    refine ⟨count, packed, countVal, ?_, splitBack_length _ _ _, ?_⟩
    · simp only [normalize_rows, core.slice.Slice.iter, CandidateRowsRuntime.mapNew, bind_ok, total, empty, ite_false]
      rw [doubled, bind_ok, split, bind_ok]
      dsimp! only
      rw [show core.slice.Slice.split_at_mut (prefixSlice storage (2 * count.val)) count =
        .ok ((ids, temporary), splitBack arrays count.val) from splitArrays, bind_ok]
      dsimp! only
      rw [show core.slice.Slice.fill core.clone.CloneU64 (tail storage (2 * count.val)) 0#u64 =
        .ok zeroOffsets from fill_zero offsets, bind_ok]
      simp only [core.iter.traits.iterator.Iterator.enumerate.trait_default,
        core.iter.traits.iterator.Iterator.enumerate.default, bind_ok]
      rw [show normalize_rows_loop0 ⟨⟨rows, 0⟩, 0#usize⟩ zeroOffsets ids 0#usize =
        .ok (writtenOffsets, writtenIds) from outer, bind_ok]
      dsimp! only
    · intro bucket live
      obtain ⟨hints, source, model⟩ := packed_model rows count packed writtenIds temporary writtenOffsets
        used empty countVal (idsLength.trans idsLen) tempLen (by rwa [offsetsLength]) layout final bucket live
      refine ⟨hints, source, model, ?_, ?_⟩
      · rw [model]; exact normalized_row_distinct _
      · intro word
        rw [model]
        exact normalized_row_mem _ _

#print axioms native_row_local_normalize

end BulksketchBridge.CandidateNormalization
