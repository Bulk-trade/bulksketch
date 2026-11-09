import BulksketchBridge.CandidateCompactNative

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.sketch.candidates

def countMass (counts : Slice U64) : Nat := (counts.val.map UScalar.val).sum

def offsetAt (counts : Slice U64) (index : Nat) : Nat :=
  ((counts.val.take (index + 1)).map UScalar.val).sum

private theorem prefix_sum_le (words : List U64) (size : Nat) :
    ((words.take size).map UScalar.val).sum ≤ (words.map UScalar.val).sum := by
  conv_rhs => rw [← List.take_append_drop size words, List.map_append, List.sum_append]
  exact Nat.le_add_right _ _

theorem offset_bounded (counts : Slice U64) (index : Nat) : offsetAt counts index ≤ countMass counts :=
  prefix_sum_le _ _

theorem offset_mono (counts : Slice U64) {left right : Nat} (order : left ≤ right) :
    offsetAt counts left ≤ offsetAt counts right := by
  have bound := prefix_sum_le (counts.val.take (right + 1)) (left + 1)
  rw [List.take_take, Nat.min_eq_left (by omega)] at bound
  exact bound

private theorem offset_succ (counts : Slice U64) (index : Nat) (room : index + 1 < counts.length) :
    offsetAt counts (index + 1) = offsetAt counts index + counts[index + 1]!.val := by
  have active : index + 1 < counts.val.length := room
  unfold offsetAt
  rw [List.take_succ_eq_append_getElem active, List.Inhabited_getElem_eq_getElem! _ _ active,
    List.map_append, List.sum_append, Slice.getElem!_Nat_eq]
  rfl

private theorem offset_zero (counts : Slice U64) (positive : 0 < counts.length) :
    offsetAt counts 0 = counts[0]!.val := by
  have active : 0 < counts.val.length := positive
  unfold offsetAt
  rw [show 0 + 1 = 1 from rfl, List.take_succ_eq_append_getElem active,
    List.Inhabited_getElem_eq_getElem! _ _ active, Slice.getElem!_Nat_eq]
  rfl

/-- Entries through the current source bucket are cumulative offsets.
Every later word is still its original count. -/
def OffsetInvariant (counts current : Slice U64) (bucket : Nat) : Prop :=
  current.length = counts.length ∧
  ∀ slot < counts.length, current[slot]!.val =
    if slot ≤ bucket then offsetAt counts slot else counts[slot]!.val

theorem offsets_initial (counts : Slice U64) : OffsetInvariant counts counts 0 := by
  refine ⟨rfl, ?_⟩
  intro slot inside
  by_cases first : slot ≤ 0
  · have zero : slot = 0 := by omega
    rw [ite_eq_left first, zero, offset_zero counts (by omega)]
  · rw [ite_eq_right first]

private theorem offsets_step (counts current : Slice U64) (cursor : core.ops.range.Range Usize)
    (active : cursor.start.val < cursor.end.val) (room : cursor.end.val < counts.length)
    (mass : countMass counts ≤ U64.max) (invariant : OffsetInvariant counts current cursor.start.val) :
    ∃ advanced written,
      normalize_loop2.body cursor current = .ok (.cont (advanced, written)) ∧
      advanced.start.val = cursor.start.val + 1 ∧ advanced.end = cursor.end ∧
      OffsetInvariant counts written advanced.start.val := by
  obtain ⟨length, entries⟩ := invariant
  obtain ⟨⟨item, advanced⟩, next, itemVal, advanceVal, endVal⟩ := RawMulTable.normal_of_spec _ _
    (core.iter.range.IteratorRange.next_Usize_some_spec cursor active)
  rw [itemVal] at next
  have max : counts.length ≤ Usize.max := counts.length_ineq
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  obtain ⟨slot, addSlot, slotVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := cursor.start) (y := 1#usize) (by rw [one]; omega))
  rw [one] at slotVal
  have previous := DenseDivRem.read_normal current cursor.start (by omega)
  have following := DenseDivRem.read_normal current slot (by rw [slotVal]; omega)
  rw [slotVal] at following
  let a := current[cursor.start.val]!
  let b := current[cursor.start.val + 1]!
  have aVal : a.val = offsetAt counts cursor.start.val := by
    simpa only [ite_eq_left (le_rfl : cursor.start.val ≤ cursor.start.val)] using entries cursor.start.val (by omega)
  have bVal : b.val = counts[cursor.start.val + 1]!.val := by
    simpa only [ite_eq_right (by omega : ¬cursor.start.val + 1 ≤ cursor.start.val)] using
      entries (cursor.start.val + 1) (by omega)
  have sumValue : b.val + a.val = offsetAt counts (cursor.start.val + 1) := by
    rw [aVal, bVal, offset_succ _ _ (by omega)]
    omega
  obtain ⟨sum, addSum, sumVal⟩ := RawMulTable.normal_of_spec _ _
    (U64.add_spec (x := b) (y := a) (by rw [sumValue]; exact (offset_bounded _ _).trans mass))
  let written := current.setAtNat (cursor.start.val + 1) sum
  have update := Reconstruction.update_normal current slot sum (by rw [slotVal]; omega)
  rw [slotVal] at update
  refine ⟨advanced, written, ?_, advanceVal, endVal, ?_⟩
  · simp only [normalize_loop2.body, next, bind_ok]
    dsimp! only
    rw [previous, bind_ok, addSlot, bind_ok, following, bind_ok]
    rw [show (current[cursor.start.val + 1]! + current[cursor.start.val]! : Result U64) = .ok sum from addSum,
      bind_ok, update, bind_ok]
  · refine ⟨(Slice.setAtNat_length _ _ _).trans length, ?_⟩
    intro index inside
    rw [advanceVal]
    by_cases same : index = cursor.start.val + 1
    · subst index
      rw [ite_eq_left le_rfl]
      have read : written[cursor.start.val + 1]! = sum := by
        simp only [written, Slice.getElem!_Nat_eq]
        exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by omega)
      rw [read, sumVal, sumValue]
    · have unchanged : written[index]! = current[index]! := by
        simp only [written, Slice.getElem!_Nat_eq]
        exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm same)
      rw [unchanged, entries index inside]
      have switch : index ≤ cursor.start.val + 1 ↔ index ≤ cursor.start.val := by omega
      simp only [switch]

/-- The original prefix-sum loop yields the exact cumulative bucket offsets
and preserves every unvisited count, with a checked global mass bound. -/
def ActualNativeCandidateOffsets : Prop :=
  ∀ (counts current : Slice U64) (cursor : core.ops.range.Range Usize),
    cursor.start.val ≤ cursor.end.val → cursor.end.val < counts.length →
    countMass counts ≤ U64.max →
    OffsetInvariant counts current cursor.start.val →
    ∃ output, normalize_loop2 cursor current = .ok output ∧ OffsetInvariant counts output cursor.end.val

theorem native_candidate_offsets : ActualNativeCandidateOffsets := by
  intro counts current cursor ordered room mass invariant
  suffices ∀ fuel (cursor : core.ops.range.Range Usize) (current : Slice U64),
      cursor.end.val - cursor.start.val = fuel →
      cursor.start.val ≤ cursor.end.val → cursor.end.val < counts.length →
      OffsetInvariant counts current cursor.start.val →
      ∃ output, normalize_loop2 cursor current = .ok output ∧ OffsetInvariant counts output cursor.end.val from
    this _ cursor current rfl ordered room invariant
  intro fuel
  induction fuel with
  | zero =>
    intro cursor current exhausted ordered room invariant
    have atEnd : cursor.start.val = cursor.end.val := by omega
    obtain ⟨⟨item, unchanged⟩, next, noMore, _⟩ := RawMulTable.normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_none_spec cursor (by omega))
    rw [noMore] at next
    have stop : normalize_loop2.body cursor current = .ok (.done current) := by
      simp only [normalize_loop2.body, next, bind_ok]
      rfl
    refine ⟨current, ?_, atEnd ▸ invariant⟩
    unfold normalize_loop2 loop
    dsimp only
    rw [stop, bind_ok]
  | succ fuel ih =>
    intro cursor current remaining ordered room invariant
    have active : cursor.start.val < cursor.end.val := by omega
    obtain ⟨advanced, written, step, advanceVal, endVal, preserved⟩ :=
      offsets_step counts current cursor active room mass invariant
    obtain ⟨output, rest, final⟩ := ih advanced written (by rw [advanceVal, endVal]; omega)
      (by rw [advanceVal, endVal]; omega) (by rwa [endVal]) preserved
    refine ⟨output, ?_, by rwa [endVal] at final⟩
    unfold normalize_loop2 loop
    dsimp only
    rw [step, bind_ok]
    exact rest

#print axioms native_candidate_offsets

end BulksketchBridge.CandidateNormalization
