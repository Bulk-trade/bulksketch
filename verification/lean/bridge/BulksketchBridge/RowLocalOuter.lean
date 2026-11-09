import BulksketchBridge.RowLocalStep
import BulksketchBridge.RowLocalCount
import BulksketchBridge.CandidateBucket

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.sketch.candidates

def rowHints {F : Type} (rows : List (DecodeRow F)) : List (Slice U64) :=
  rows.map (fun row => row.candidates)

def rowPrefixWords {F : Type} (rows : Slice (DecodeRow F)) (position : Nat) : List U64 :=
  localPayload (rowHints (rows.val.take position))

def RowLocalPrefix {F : Type} (rows : Slice (DecodeRow F)) (position used : Nat)
    (offsets ids : Slice U64) : Prop :=
  used = (rowPrefixWords rows position).length ∧
  used ≤ rawRowCount (rows.val.take position) ∧
  ids.val.take used = rowPrefixWords rows position ∧
  ∀ bucket ≤ position, offsets[bucket]!.val = (rowPrefixWords rows bucket).length

private theorem take_row {F : Type} (rows : Slice (DecodeRow F)) (position : Nat)
    (active : position < rows.length) :
    rows.val.take (position + 1) = rows.val.take position ++ [rows[position]'active] := by
  exact List.take_succ_eq_append_getElem (show position < rows.val.length from active)

private theorem count_add {F : Type} (left right : List (DecodeRow F)) :
    rawRowCount (left ++ right) = rawRowCount left + rawRowCount right := by
  simp only [rawRowCount, List.map_append, List.sum_append]

private theorem raw_prefix_le {F : Type} (rows : List (DecodeRow F)) (count : Nat) :
    rawRowCount (rows.take count) ≤ rawRowCount rows := by
  conv_rhs => rw [← List.take_append_drop count rows, count_add]
  exact Nat.le_add_right _ _

private theorem prefix_succ {F : Type} (rows : Slice (DecodeRow F)) (position : Nat)
    (active : position < rows.length) :
    rowPrefixWords rows (position + 1) = rowPrefixWords rows position ++ normalizedRowWords rows[position].candidates := by
  simp only [rowPrefixWords, take_row rows position active, rowHints, List.map_append, List.map_cons,
    List.map_nil, localPayload, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The actual outer loop keeps one distinct normalized segment per row,
retains previous rows and commits the exact cumulative offset at each step. -/
def ActualNativeRowLocalOuter : Prop :=
  ∀ {F : Type} (rows : Slice (DecodeRow F)) (position : Nat) (bucket used : Usize) (offsets ids : Slice U64),
    position ≤ rows.length → bucket.val = position →
    rows.length + 1 ≤ offsets.length → rawRowCount rows.val ≤ ids.length →
    RowLocalPrefix rows position used.val offsets ids →
    ∃ finalOffsets finalIds finalUsed,
      normalize_rows_loop0 (⟨⟨rows, position⟩, bucket⟩ : RowIterator F) offsets ids used =
        .ok (finalOffsets, finalIds) ∧
      finalOffsets.length = offsets.length ∧ finalIds.length = ids.length ∧
      RowLocalPrefix rows rows.length finalUsed finalOffsets finalIds

private theorem outer_done {F : Type} (rows : Slice (DecodeRow F)) (position : Nat)
    (bucket used : Usize) (offsets ids : Slice U64) (inactive : ¬ position < rows.length) :
    normalize_rows_loop0 (⟨⟨rows, position⟩, bucket⟩ : RowIterator F) offsets ids used =
      .ok (offsets, ids) := by
  have noNext : core.slice.iter.IteratorSliceIter.next ⟨rows, position⟩ = .ok (none, ⟨rows, position⟩) := by
    have no : ¬position < rows.len.val := by rwa [Slice.len_val]
    simp only [core.slice.iter.IteratorSliceIter.next, no, _root_.dite_false]
  have next : core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (DecodeRow F)) (⟨⟨rows, position⟩, bucket⟩ : RowIterator F)
        = .ok (none, ⟨⟨rows, position⟩, bucket⟩) := by
    simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, noNext, bind_ok]
    rfl
  have stop : normalize_rows_loop0.body (⟨⟨rows, position⟩, bucket⟩ : RowIterator F) offsets ids used =
      .ok (.done (offsets, ids)) := by
    simp only [normalize_rows_loop0.body, next, bind_ok]
    rfl
  unfold normalize_rows_loop0 loop
  dsimp only
  rw [stop, bind_ok]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2200000 in
theorem native_row_local_outer : ActualNativeRowLocalOuter := by
  intro F rows position bucket used offsets ids room aligned offsetsRoom inputRoom prefixFrame
  suffices ∀ fuel position (bucket used : Usize) (offsets ids : Slice U64),
    rows.length - position = fuel → position ≤ rows.length → bucket.val = position →
    rows.length + 1 ≤ offsets.length → rawRowCount rows.val ≤ ids.length →
    RowLocalPrefix rows position used.val offsets ids →
    ∃ finalOffsets finalIds finalUsed,
      normalize_rows_loop0 (⟨⟨rows, position⟩, bucket⟩ : RowIterator F) offsets ids used =
        .ok (finalOffsets, finalIds) ∧
      finalOffsets.length = offsets.length ∧ finalIds.length = ids.length ∧
      RowLocalPrefix rows rows.length finalUsed finalOffsets finalIds from
    this _ position bucket used offsets ids rfl room aligned offsetsRoom inputRoom prefixFrame
  intro fuel
  induction fuel with
  | zero =>
    intro position bucket used offsets ids exhausted room aligned offsetsRoom inputRoom prefixFrame
    have endAt : position = rows.length := by omega
    exact ⟨offsets, ids, used.val, outer_done rows position bucket used offsets ids (by omega),
      rfl, rfl, endAt ▸ prefixFrame⟩
  | succ fuel ih =>
    intro position bucket used offsets ids remaining room aligned offsetsRoom inputRoom prefixFrame
    have active : position < rows.length := by omega
    obtain ⟨counted, usedBound, wordPrefix, stored⟩ := prefixFrame
    let hints := (rows[position]'active).candidates
    have rawNext : rawRowCount (rows.val.take (position + 1)) =
        rawRowCount (rows.val.take position) + hints.length := by
      rw [take_row rows position active, count_add]
      rfl
    have rawFits := raw_prefix_le rows.val (position + 1)
    have room : used.val + hints.length ≤ ids.length := by omega
    obtain ⟨newBucket, newUsed, counts, written, step, bucketVal, usedVal, nextRoom, writtenLen,
      writtenPrefix, countEq⟩ :=
      native_row_local_step rows position bucket used offsets ids active aligned (by omega) room
    change newUsed.val ≤ used.val + hints.length at nextRoom
    have countsLen : counts.length = offsets.length := by rw [countEq, Slice.setAtNat_length]
    have combined : RowLocalPrefix rows (position + 1) newUsed.val counts written := by
      have nextPrefix := prefix_succ rows position active
      refine ⟨?_, by rw [rawNext]; omega, ?_, ?_⟩
      · rw [usedVal, counted, nextPrefix, List.length_append]
      · rw [writtenPrefix, wordPrefix, nextPrefix]
      · intro slot bound
        rw [countEq]
        by_cases last : slot = position + 1
        · subst slot
          have recorded :
              (offsets.setAtNat (position + 1) (UScalar.cast .U64 newUsed))[position + 1]! =
                UScalar.cast .U64 newUsed := by
            simp only [Slice.getElem!_Nat_eq]
            exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by omega)
          rw [recorded, UScalar.cast_val_eq]
          change newUsed.val % (2 ^ 64) = _
          rw [Nat.mod_eq_of_lt (usize_fits_u64 newUsed), usedVal, counted, nextPrefix, List.length_append]
        · have kept : (offsets.setAtNat (position + 1) (UScalar.cast .U64 newUsed))[slot]! =
              offsets[slot]! := by
            simp only [Slice.getElem!_Nat_eq]
            exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm last)
          rw [kept]
          exact stored slot (by omega)
    obtain ⟨finalOffsets, finalIds, finalUsed, ran, finalOffsetsLen, finalIdsLen, final⟩ :=
      ih (position + 1) newBucket newUsed counts written (by omega) (by omega)
        bucketVal (by rwa [countsLen]) (by rwa [writtenLen]) combined
    refine ⟨finalOffsets, finalIds, finalUsed, ?_, finalOffsetsLen.trans countsLen,
      finalIdsLen.trans writtenLen, final⟩
    unfold normalize_rows_loop0 loop
    dsimp only
    rw [step, bind_ok]
    exact ran

#print axioms native_row_local_outer

end BulksketchBridge.CandidateNormalization
