import BulksketchBridge.PublicationWrite
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.PublicationWrite

open Aeneas Aeneas.Std Result Error
open Aeneas.Std.PublicationWriteRuntime Aeneas.Std.CanonicalizeRuntime
open bulksketch.sketch.api bulksketch.sketch.scratch bulksketch.types
open BulksketchBridge.CanonicalizeOrdering

set_option maxRecDepth 4096
set_option maxHeartbeats 4500000

def zeroWidth (zero : Bool) : Nat := if zero then 1 else 0

def withZero (ids : Slice U64) (used : Usize) (zero : Bool) : Slice U64 :=
  if zero then ids.set used 0#u64 else ids

def decodedFrame (before : Publication) (bucket endIds next count : Usize)
    (ids : Slice U64) (zero : Bool) : Publication :=
  let out : StoredOutcome :=
    ⟨.Decoded, UScalar.cast .U64 before.used_ids, UScalar.cast .U64 count⟩
  { before with
    results := {
      ids := (withZero before.results.ids before.used_ids zero).setSlice!
        (before.used_ids.val + zeroWidth zero) ids.val
      outcomes := before.results.outcomes.set bucket out }
    written := next
    used_ids := endIds }

/-- The checked original decoded writer appends exactly the optional original
zero and the source roots, and advances the committed row and word counters. -/
def ActualPublicationWriteDecoded : Prop :=
  ∀ (before : Publication) (bucket : Usize) (ids : Slice U64) (zero : Bool),
    RowAdmission before bucket → validDecoded ids zero →
    before.used_ids.val + zeroWidth zero + ids.length ≤ before.id_capacity.val →
    before.used_ids.val + zeroWidth zero + ids.length ≤ before.results.ids.length →
    ∃ endIds next count : Usize,
      endIds.val = before.used_ids.val + zeroWidth zero + ids.length ∧
      next.val = before.written.val + 1 ∧ count.val = zeroWidth zero + ids.length ∧
      Publication.write before bucket (.Decoded ids) zero =
        .ok (decodedFrame before bucket endIds next count ids zero, back before)

private theorem copy_one_then {T : Type} (destination ids : Slice U64)
    (one : ids.length = 1) (room : destination.length = ids.length)
    (finish : Slice U64 → Result T) :
    (do
      let word ← Slice.index_usize ids 0#usize
      let written ← Slice.update destination 0#usize word
      finish written) = finish ids := by
  simp only [Bind.bind, ← Aeneas.Std.bind_assoc]
  have copy := one_copy destination ids one room
  simp only [Bind.bind] at copy
  rw [copy, bind_ok]

private theorem copy_two_then {T : Type} (destination ids : Slice U64)
    (two : ids.length = 2) (room : destination.length = ids.length)
    (finish : Slice U64 → Result T) :
    (do
      let first ← Slice.index_usize ids 0#usize
      let second ← Slice.index_usize ids 1#usize
      let written ← Slice.update destination 0#usize first
      let written2 ← Slice.update written 1#usize second
      finish written2) = finish ids := by
  simp only [Bind.bind, ← Aeneas.Std.bind_assoc]
  have copy := two_copy destination ids two room
  simp only [Bind.bind] at copy
  rw [copy, bind_ok]

theorem write_decoded_refines : ActualPublicationWriteDecoded := by
  intro before bucket ids zero admission valid capFits storageFits
  obtain ⟨clear, ordered, row, storage, nextFits⟩ := admission
  subst bucket
  let pre := core.convert.num.FromUsizeBool.from zero
  have preValue : pre.val = zeroWidth zero := by cases zero <;> rfl
  have totalFits : before.used_ids.val + zeroWidth zero + ids.length ≤ Usize.max :=
    storageFits.trans before.results.ids.length_ineq
  have startFits : before.used_ids.val + pre.val ≤ Usize.max := by rw [preValue]; omega
  obtain ⟨start, addStart, startValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := before.used_ids) (y := pre) startFits)
  have checkStart : Usize.checked_add before.used_ids pre = some start := by
    change Option.ofResult (before.used_ids + pre : Result Usize) = _
    rw [addStart]
    rfl
  obtain ⟨endIds, checkEnd, endValue⟩ := RootDivideArithmetic.add_fits start ids.len (by
    rw [startValue, Slice.len_val, preValue]
    exact totalFits)
  have endExact : endIds.val = before.used_ids.val + zeroWidth zero + ids.length := by
    rw [endValue, startValue, preValue, Slice.len_val]
  have withinCapacity : endIds ≤ before.id_capacity := by
    change endIds.val ≤ before.id_capacity.val
    omega
  have endOrder : before.used_ids ≤ endIds := by
    change before.used_ids.val ≤ endIds.val
    omega
  obtain ⟨count, subNormal, countVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := endIds) (y := before.used_ids) endOrder)
  have countExact : count.val = zeroWidth zero + ids.length := by
    have exact := countVal.1
    omega
  obtain ⟨next, incNormal, incVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := before.written) (y := 1#usize) nextFits)
  let stored : StoredOutcome := ⟨.Decoded, UScalar.cast .U64 before.used_ids, UScalar.cast .U64 count⟩
  have writeOutcome := write_at before.results.outcomes before.written stored storage
  have bound : before.written < before.rows := row
  have computeEnd :
      andThen Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize
        (some start) ids = .ok (some endIds) := by
    simp only [andThen, Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize,
      Publication.write.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once, checkEnd]
  obtain ⟨unused, windowNormal⟩ := window_check ids
  have noZero := nonzero_head ids valid.2.1
  have windowsValid := valid.2.2
  have validateNonempty : (!ids.val.isEmpty || zero) = true := by
    rcases valid.1 with nonempty | hasZero
    · have b : ids.val.isEmpty = false := by simpa using nonempty
      simp [b]
    · simp [hasZero]
  have assertNonempty : (decide (¬ ids.val.isEmpty = true) || zero) = true := by
    cases h : ids.val.isEmpty <;> simpa [h] using validateNonempty
  have emptyNormal : core.slice.Slice.is_empty ids = .ok ids.val.isEmpty := by
    unfold core.slice.Slice.is_empty
    simp only [Slice.len_val, Slice.length, List.length_eq_zero_iff]
    cases ids.val <;> rfl
  have idWidth : (withZero before.results.ids before.used_ids zero).length = before.results.ids.length := by
    cases zero <;> simp [withZero, Slice.set, Slice.setAtNat, Slice.length]
  have sliceOrder : start.val ≤ endIds.val := by rw [endValue]; omega
  have sliceRoom : endIds.val ≤ (withZero before.results.ids before.used_ids zero).length := by
    rw [idWidth, endExact]
    exact storageFits
  have range := ClosedLeaf.mutable_region_normal
    (withZero before.results.ids before.used_ids zero) start endIds sliceOrder sliceRoom
  let destination := ClosedLeaf.region (withZero before.results.ids before.used_ids zero) start.val endIds.val
  have destinationLen : destination.length = ids.length := by
    rw [ClosedLeaf.region_length _ _ _ sliceRoom, endValue, Slice.len_val]
    omega
  have copy := ClosedLeaf.copy_normal destination ids destinationLen
  have zeroStore : zero = true →
      Slice.update before.results.ids before.used_ids 0#u64 =
        .ok (withZero before.results.ids before.used_ids zero) := by
    intro hz
    rw [write_at before.results.ids before.used_ids 0#u64 (by
      have : zeroWidth zero = 1 := by simp [zeroWidth, hz]
      omega)]
    simp [withZero, hz]
  refine ⟨endIds, next, count, endExact, incVal, countExact, ?_⟩
  unfold Publication.write
  simp only [clear, core.option.Option.is_none, Option.isNone, massert, ite_true, bound,
    bind_ok, emptyNormal, assertNonempty, PublicationWriteRuntime.first, noZero,
    CanonicalizeRuntime.windows, windowNormal, windowsValid, pre, checkStart, computeEnd,
    core.option.Option.expect, ofOption, withinCapacity, lift, addStart,
    Slice.index_mut_SliceIndexRangeUsizeSliceInst, range]
  by_cases idsEmpty : ids.val.isEmpty = true <;> simp only [idsEmpty, ite_true, ite_false]
  all_goals
    dsimp! only
    simp only [withinCapacity, ite_true, bind_ok, ofOption]
    cases zero
  all_goals
    simp only [withZero, Bool.false_eq_true, ite_false, ite_true] at range
    simp only [Bool.false_eq_true, ite_false, ite_true, zeroStore, withZero, bind_ok, range]
    dsimp! only
  all_goals
    first
    | rw [show ClosedLeaf.region before.results.ids start.val endIds.val = destination from rfl]
    | rw [show ClosedLeaf.region (before.results.ids.set before.used_ids 0#u64)
            start.val endIds.val = destination from rfl]
  all_goals by_cases one : ids.len = 1#usize
  all_goals by_cases two : ids.len = 2#usize
  all_goals
    first
    | have oneLength : ids.length = 1 := by rw [← Slice.len_val, one]; rfl
      simp only [ite_eq_left one, copy_one_then destination ids oneLength destinationLen]
    | have twoLength : ids.length = 2 := by rw [← Slice.len_val, two]; rfl
      simp only [ite_eq_right one, ite_eq_left two, copy_two_then destination ids twoLength destinationLen]
    | simp only [ite_eq_right one, ite_eq_right two, copy, bind_ok]
  all_goals
    simp only [stored] at writeOutcome
    simp only [RootDivideArithmetic.offset_word, bind_ok, core.result.Result.expect, subNormal,
      incNormal, writeOutcome, decodedFrame, startValue, preValue, withZero, Bool.false_eq_true,
      ite_false, ite_true, back, clear]
  all_goals
    apply congrArg Result.ok
    congr 1
    funext later
    simp [back, clear]

/-- Original status-only and valid decoded publication writes. Row admission,
strict root validation and destination capacity remain explicit premises. -/
def ActualPublicationWrite : Prop :=
  (∀ before bucket zero, RowAdmission before bucket →
    ∃ next : Usize, next.val = before.written.val + 1 ∧
      Publication.write before bucket .Equal zero =
        .ok (appendStatus before bucket next .Equal, back before) ∧
      ∀ reason, Publication.write before bucket (.Failed reason) zero =
        .ok (appendStatus before bucket next (status reason), back before)) ∧
  (∀ (before : Publication) (bucket : Usize) (ids : Slice U64) (zero : Bool),
    RowAdmission before bucket → validDecoded ids zero →
    before.used_ids.val + zeroWidth zero + ids.length ≤ before.id_capacity.val →
    before.used_ids.val + zeroWidth zero + ids.length ≤ before.results.ids.length →
    ∃ endIds next count : Usize,
      endIds.val = before.used_ids.val + zeroWidth zero + ids.length ∧
      next.val = before.written.val + 1 ∧ count.val = zeroWidth zero + ids.length ∧
      Publication.write before bucket (.Decoded ids) zero =
        .ok (decodedFrame before bucket endIds next count ids zero, back before))

theorem write_refines : ActualPublicationWrite :=
  ⟨write_status_refines, write_decoded_refines⟩

#print axioms write_refines

#print axioms write_decoded_refines

end BulksketchBridge.PublicationWrite
