import BulksketchBridge.RowLocalContents
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open Aeneas.Std.DegreeProbeRuntime
open bulksketch.sketch.candidates

abbrev RowIterator (F : Type) := core.iter.adapters.enumerate.Enumerate
  (core.slice.iter.Iter (bulksketch.sketch.input.DecodeRow F))

private theorem pasted (words : Slice U64) (start : Nat) (segment : List U64)
    (room : start + segment.length ≤ words.length) :
    (words.setSlice! start segment).val = words.val.take start ++ segment ++ words.val.drop (start + segment.length) := by
  have fits : segment.length ≤ words.val.length - start := by
    change start + segment.length ≤ words.val.length at room
    omega
  rw [Slice.setSlice!_val]
  simp only [List.setSlice!, Nat.min_eq_left fits, List.take_length]

private theorem pasted_prefix (words : Slice U64) (start : Nat) (segment : List U64)
    (room : start + segment.length ≤ words.length) :
    (words.setSlice! start segment).val.take start = words.val.take start := by
  have fits : start ≤ words.val.length := by
    change start + segment.length ≤ words.val.length at room
    omega
  have size : (words.val.take start).length = start := by rw [List.length_take, Nat.min_eq_left fits]
  rw [pasted _ _ _ room, List.append_assoc]
  simpa only [size] using (List.take_left (l₁ := words.val.take start)
    (l₂ := segment ++ words.val.drop (start + segment.length)))

private theorem pasted_segment (words : Slice U64) (start : Nat) (segment : List U64)
    (room : start + segment.length ≤ words.length) :
    (words.setSlice! start segment).val.slice start (start + segment.length) = segment := by
  have fits : start ≤ words.val.length := by
    change start + segment.length ≤ words.val.length at room
    omega
  have size : (words.val.take start).length = start := by rw [List.length_take, Nat.min_eq_left fits]
  rw [pasted _ _ _ room, List.append_assoc]
  unfold List.slice
  rw [Nat.add_sub_cancel_left]
  have dropped : (words.val.take start ++ (segment ++ words.val.drop (start + segment.length))).drop start =
      segment ++ words.val.drop (start + segment.length) := by
    simpa only [size] using (List.drop_left (l₁ := words.val.take start)
      (l₂ := segment ++ words.val.drop (start + segment.length)))
  rw [dropped, List.take_left]

/-- One original row iteration copies and sorts its own range, compacts
within that range and commits exactly one cumulative output offset. -/
def ActualNativeRowLocalStep : Prop :=
  ∀ {F : Type} (rows : Slice (bulksketch.sketch.input.DecodeRow F))
    (position : Nat) (bucket used : Usize) (offsets ids : Slice U64)
    (active : position < rows.length),
    bucket.val = position → position + 1 < offsets.length →
    used.val + rows[position].candidates.length ≤ ids.length →
    ∃ newBucket newUsed counts written,
      normalize_rows_loop0.body (⟨⟨rows, position⟩, bucket⟩ : RowIterator F) offsets ids used =
        .ok (.cont (⟨⟨rows, position + 1⟩, newBucket⟩, counts, written, newUsed)) ∧
      newBucket.val = position + 1 ∧
      newUsed.val = used.val + (normalizedRowWords rows[position].candidates).length ∧
      newUsed.val ≤ used.val + rows[position].candidates.length ∧
      written.length = ids.length ∧
      written.val.take newUsed.val = ids.val.take used.val ++ normalizedRowWords rows[position].candidates ∧
      counts = offsets.setAtNat (position + 1) (UScalar.cast .U64 newUsed)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
theorem native_row_local_step : ActualNativeRowLocalStep := by
  intro F rows position bucket used offsets ids active aligned countRoom room
  let row := rows[position]'active
  let hints := row.candidates
  change used.val + hints.length ≤ ids.length at room
  have offsetMax : offsets.length ≤ Usize.max := offsets.length_ineq
  have idsMax : ids.length ≤ Usize.max := ids.length_ineq
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  obtain ⟨newBucket, bump, newBucketVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := bucket) (y := 1#usize) (by rw [aligned, one]; omega))
  rw [aligned, one] at newBucketVal
  have rowNext : core.slice.iter.IteratorSliceIter.next ⟨rows, position⟩ =
      .ok (some row, ⟨rows, position + 1⟩) := by
    have fits : position < rows.len.val := by rwa [Slice.len_val]
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dite_eq_left fits]
    rfl
  have next : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (bulksketch.sketch.input.DecodeRow F))
      (⟨⟨rows, position⟩, bucket⟩ : RowIterator F) =
      .ok (some (bucket, row), ⟨⟨rows, position + 1⟩, newBucket⟩) := by
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, rowNext, bind_ok]
    dsimp! only
    rw [bump, bind_ok]
  have hintsLen : hints.len.val = hints.length := Slice.len_val _
  obtain ⟨stop, endCall, stopVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := used) (y := hints.len) (by rw [hintsLen]; omega))
  rw [hintsLen] at stopVal
  have ordered : used.val ≤ stop.val := by omega
  have stopFits : stop.val ≤ ids.length := by omega
  have copyCut := ClosedLeaf.mutable_region_normal ids used stop ordered stopFits
  have copyLen : (ClosedLeaf.region ids used.val stop.val).length = hints.length := by
    rw [ClosedLeaf.region_length _ _ _ stopFits]
    omega
  have copyCall := ClosedLeaf.copy_normal (ClosedLeaf.region ids used.val stop.val) hints copyLen
  let copied := ids.setSlice! used.val hints.val
  have copiedLen : copied.length = ids.length := Slice.setSlice!_length _ _ _
  have sortCut := ClosedLeaf.mutable_region_normal copied used stop ordered (by rw [copiedLen]; exact stopFits)
  have copiedRegion : ClosedLeaf.region copied used.val stop.val = hints := by
    apply Slice.ext
    simp only [ClosedLeaf.region, Slice.from_val, stopVal]
    exact pasted_segment ids used.val hints.val room
  let sorted := sortedWords hints
  let sortedIds := copied.setSlice! used.val sorted.val
  have sortedIdsLen : sortedIds.length = ids.length := (Slice.setSlice!_length _ _ _).trans copiedLen
  obtain ⟨written, newUsed, compacted, compactLength, lower, upper, compactWords, oldWords⟩ :=
    native_row_local_compacted_slice sortedIds used stop ordered (by rw [sortedIdsLen]; exact stopFits)
  have sortedRoom : used.val + sorted.val.length ≤ copied.length := by
    change used.val + sorted.length ≤ copied.length
    rw [BulksketchBridge.DegreeProbeRuntime.sortedWords_length, copiedLen]
    exact room
  have sortedSegment : sortedIds.val.slice used.val stop.val = sorted.val := by
    rw [stopVal, ← show sorted.length = hints.length from BulksketchBridge.DegreeProbeRuntime.sortedWords_length _]
    exact pasted_segment copied used.val sorted.val sortedRoom
  have normalized : written.val.slice used.val newUsed.val = normalizedRowWords hints := by
    rw [compactWords, sortedSegment]
    rfl
  have retainedLength : (written.val.slice used.val newUsed.val).length = newUsed.val - used.val := by
    have usedFits : newUsed.val ≤ written.val.length := by
      change newUsed.val ≤ written.length
      rw [compactLength, sortedIdsLen]
      exact upper.trans stopFits
    rw [List.slice_length, Nat.min_eq_right (Nat.sub_le_sub_right usedFits _)]
  have countExact : newUsed.val = used.val + (normalizedRowWords hints).length := by
    rw [normalized] at retainedLength
    omega
  have old : written.val.take used.val = ids.val.take used.val := by
    rw [oldWords]
    exact (pasted_prefix copied used.val sorted.val sortedRoom).trans (pasted_prefix ids used.val hints.val room)
  have combined : written.val.take newUsed.val = ids.val.take used.val ++ normalizedRowWords hints := by
    have split : written.val.take newUsed.val =
        written.val.take used.val ++ written.val.slice used.val newUsed.val := by
      unfold List.slice
      rw [← List.take_add, Nat.add_sub_of_le lower]
    rw [split, old, normalized]
  let counts := offsets.setAtNat (position + 1) (UScalar.cast .U64 newUsed)
  have recorded := Reconstruction.update_normal offsets newBucket (UScalar.cast .U64 newUsed)
    (by rw [newBucketVal]; exact countRoom)
  rw [newBucketVal] at recorded
  refine ⟨newBucket, newUsed, counts, written, ?_, newBucketVal, countExact,
    by rw [← stopVal]; exact upper, compactLength.trans sortedIdsLen, combined, rfl⟩
  simp only [normalize_rows_loop0.body, next, bind_ok]
  dsimp! only
  rw [show (used + row.candidates.len : Result Usize) = .ok stop from endCall, bind_ok]
  simp only [core.slice.index.Slice.index_mut, copyCut, bind_ok]
  dsimp! only
  rw [show core.slice.Slice.copy_from_slice core.marker.CopyU64 (ClosedLeaf.region ids used.val stop.val)
    row.candidates = .ok hints from copyCall, bind_ok]
  rw [show core.slice.index.SliceIndexRangeUsizeSlice.index_mut ⟨used, stop⟩
    (ids.setSlice! used.val hints.val) =
      .ok (ClosedLeaf.region copied used.val stop.val, fun replacement => copied.setSlice! used.val replacement.val)
    from sortCut, bind_ok]
  dsimp! only
  rw [copiedRegion]
  rw [show sortUnsigned hints = .ok sorted from rfl, bind_ok]
  rw [show normalize_rows_loop0_loop0 ⟨used, stop⟩ sortedIds used used = .ok (written, newUsed) from compacted,
    bind_ok]
  dsimp! only
  rw [bump, bind_ok, lift, bind_ok, recorded, bind_ok]

#print axioms native_row_local_step

end BulksketchBridge.CandidateNormalization
