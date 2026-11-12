import BulksketchBridge.CandidateBucket
import BulksketchBridge.CandidateCompactWords
import BulksketchBridge.DenseDivRemControl
import BulksketchBridge.AffineSelector

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open ClosedLeafAdvance (usizeWord word_val)
open bulksketch.sketch.candidates bulksketch.sketch.shape

structure CompactState where
  offsets : Slice U64
  ids : Slice U64
  used : Nat

def addCompacted (buckets : Nat) (state : CompactState) (id : U64) : CompactState :=
  let slot := id.val % buckets + 1
  { offsets := state.offsets.setAtNat slot (AffineSelector.word (state.offsets[slot]!.val + 1))
    ids := state.ids.setAtNat state.used id
    used := state.used + 1 }

def compactAt (buckets : Nat) (index : Nat) (state : CompactState) : CompactState :=
  let id := state.ids[index]!
  if id = 0#u64 ∨ (state.used ≠ 0 ∧ state.ids[state.used - 1]! = id)
  then state else addCompacted buckets state id

def CompactBounds (buckets index : Nat) (state : CompactState) : Prop :=
  0 < buckets ∧ buckets + 1 ≤ state.offsets.length ∧
  state.used ≤ index ∧ index ≤ state.ids.length ∧
  ∀ slot < state.offsets.length, state.offsets[slot]!.val ≤ state.used

private theorem usizeMax_le_u64 : Usize.max ≤ U64.max := by
  rcases Usize.bounds_eq with bound | bound
  · rw [bound, U32.max_eq, U64.max_eq]; decide
  · rw [bound]

private theorem usize_val_max (value : Usize) : value.val ≤ Usize.max := by
  have limit := value.hBounds
  change value.val < 2 ^ System.Platform.numBits at limit
  simp only [Usize.max, Usize.numBits]
  change value.val ≤ 2 ^ System.Platform.numBits - 1
  omega

private theorem usize_add_one (value : Usize) (fits : value.val + 1 ≤ Usize.max) :
    (value + 1#usize : Result Usize) = .ok (usizeWord (value.val + 1)) := by
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  obtain ⟨output, call, outVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := value) (y := 1#usize) (by rw [one]; exact fits))
  rw [one] at outVal
  rw [call]
  exact congrArg Result.ok (UScalar.eq_of_val_eq (outVal.trans (word_val _ fits).symm))

private theorem usize_sub_one (value : Usize) (positive : 0 < value.val) :
    (value - 1#usize : Result Usize) = .ok (usizeWord (value.val - 1)) := by
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  obtain ⟨output, call, outVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := value) (y := 1#usize) (by rw [one]; exact positive))
  rw [one] at outVal
  rw [call]
  exact congrArg Result.ok (UScalar.eq_of_val_eq
    (outVal.trans (word_val _ ((Nat.sub_le ..).trans (usize_val_max value))).symm))

private theorem u64_add_one (value : U64) (fits : value.val + 1 ≤ U64.max) :
    (value + 1#u64 : Result U64) = .ok (AffineSelector.word (value.val + 1)) := by
  obtain ⟨output, call, outVal⟩ := RawMulTable.normal_of_spec _ _
    (U64.add_spec (x := value) (y := 1#u64) fits)
  rw [call]
  exact congrArg Result.ok (UScalar.eq_of_val_eq (outVal.trans (AffineSelector.word_val _ fits).symm))

private theorem inserted_bounds (buckets index : Nat) (state : CompactState) (id : U64)
    (bounds : CompactBounds buckets index state) (active : index < state.ids.length) :
    CompactBounds buckets (index + 1) (addCompacted buckets state id) := by
  obtain ⟨positive, offsetRoom, usedRoom, _, countBound⟩ := bounds
  let slot := id.val % buckets + 1
  have slotRoom : slot < state.offsets.length := by
    have inside := Nat.mod_lt id.val positive
    omega
  have nextFits : state.offsets[slot]!.val + 1 ≤ U64.max := by
    have count := countBound slot slotRoom
    have max : state.ids.length ≤ Usize.max := state.ids.length_ineq
    have := usizeMax_le_u64
    omega
  refine ⟨positive, ?_, by simpa only [addCompacted] using Nat.succ_le_succ usedRoom, ?_, ?_⟩
  · simpa only [addCompacted, Slice.setAtNat_length] using offsetRoom
  · simpa only [addCompacted, Slice.setAtNat_length] using (Nat.succ_le_of_lt active)
  · intro position inRange
    change position < (state.offsets.setAtNat slot (AffineSelector.word (state.offsets[slot]!.val + 1))).length at inRange
    rw [Slice.setAtNat_length] at inRange
    change (state.offsets.setAtNat slot (AffineSelector.word (state.offsets[slot]!.val + 1)))[position]!.val ≤
      state.used + 1
    by_cases same : slot = position
    · subst position
      rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ slotRoom,
        AffineSelector.word_val _ nextFits]
      exact Nat.succ_le_succ (countBound slot slotRoom)
    · have sameWord :
          (state.offsets.setAtNat slot (AffineSelector.word (state.offsets[slot]!.val + 1)))[position]! =
            state.offsets[position]! := by
        simp only [Slice.getElem!_Nat_eq]
        exact Slice.getElem!_Nat_setAtNat_ne state.offsets slot position _ same
      rw [sameWord]
      exact (countBound position inRange).trans (Nat.le_succ _)

private theorem skipped_bounds (buckets index : Nat) (state : CompactState)
    (bounds : CompactBounds buckets index state) (active : index < state.ids.length) :
    CompactBounds buckets (index + 1) state := by
  exact ⟨bounds.1, bounds.2.1, bounds.2.2.1.trans (Nat.le_succ _), active, bounds.2.2.2.2⟩

/-- An exact live compaction step. Every admitted branch preserves the
write-behind-read bound and the one-increment bucket-count envelope. -/
theorem native_compact_step {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (cursor : core.ops.range.Range Usize) (offsets ids : Slice U64) (used : Usize)
    (active : cursor.start.val < cursor.end.val) (inputRoom : cursor.end.val ≤ ids.length)
    (bounds : CompactBounds shape.capacities.length cursor.start.val ⟨offsets, ids, used.val⟩) :
    let next := compactAt shape.capacities.length cursor.start.val ⟨offsets, ids, used.val⟩
    ∃ advanced nextUsed,
      normalize_loop1.body field shape cursor offsets ids used =
        .ok (.cont (advanced, next.offsets, next.ids, nextUsed)) ∧
      advanced.start.val = cursor.start.val + 1 ∧ advanced.end = cursor.end ∧
      nextUsed.val = next.used ∧ next.ids.length = ids.length ∧
      CompactBounds shape.capacities.length advanced.start.val next := by
  dsimp only
  let id := ids[cursor.start.val]!
  let state : CompactState := ⟨offsets, ids, used.val⟩
  let inserted := addCompacted shape.capacities.length state id
  obtain ⟨⟨item, advanced⟩, nextCall, nextItem, nextStart, nextEnd⟩ :=
    RawMulTable.normal_of_spec _ _ (core.iter.range.IteratorRange.next_Usize_some_spec cursor active)
  rw [nextItem] at nextCall
  have read : Slice.index_usize ids cursor.start = .ok id :=
    DenseDivRem.read_normal ids cursor.start (by omega)
  have current : cursor.start.val < ids.length := by omega
  have usedLe : used.val ≤ cursor.start.val := bounds.2.2.1
  have useRoom : used.val < ids.length := by omega
  have usedFits : used.val + 1 ≤ Usize.max := useRoom.trans_le ids.length_ineq
  have usedPlus := usize_add_one used usedFits
  have wrote := Reconstruction.update_normal ids used id useRoom
  obtain ⟨bucket, route, bucketVal, bucketRoom⟩ := native_candidate_bucket field shape id bounds.1
  let slot := id.val % shape.capacities.length + 1
  have tableRoom : shape.capacities.length + 1 ≤ offsets.length := bounds.2.1
  have slotRoom : slot < offsets.length := by unfold slot; omega
  have slotFits : bucket.val + 1 ≤ Usize.max := by
    rw [bucketVal]
    exact slotRoom.le.trans offsets.length_ineq
  have slotPlus := usize_add_one bucket slotFits
  rw [bucketVal] at slotPlus
  have slotVal : (usizeWord slot).val = slot := word_val _ (slotRoom.le.trans offsets.length_ineq)
  have offsetRead := DenseDivRem.read_normal offsets (usizeWord slot) (by rw [slotVal]; exact slotRoom)
  rw [slotVal] at offsetRead
  have tallyFits : offsets[slot]!.val + 1 ≤ U64.max := by
    have tally : offsets[slot]!.val ≤ used.val := bounds.2.2.2.2 slot slotRoom
    have max : ids.length ≤ Usize.max := ids.length_ineq
    have := usizeMax_le_u64
    omega
  have tally := u64_add_one offsets[slot]! tallyFits
  have update := Reconstruction.update_normal offsets (usizeWord slot)
    (AffineSelector.word (offsets[slot]!.val + 1)) (by rw [slotVal]; exact slotRoom)
  rw [slotVal] at update
  have skipFrame := skipped_bounds shape.capacities.length cursor.start.val state bounds current
  have appendFrame := inserted_bounds shape.capacities.length cursor.start.val state id bounds current
  have basic : normalize_loop1.body field shape cursor offsets ids used = (do
      let word ← Slice.index_usize ids cursor.start
      if word != 0#u64 then
        if used = 0#usize then do
          let written ← Slice.update ids used word
          let count ← used + 1#usize
          let b ← SketchShape.bucket_for field shape word
          let addr ← b + 1#usize
          let old ← Slice.index_usize offsets addr
          let bumped ← old + 1#u64
          let next ← Slice.update offsets addr bumped
          .ok (.cont (advanced, next, written, count))
        else do
          let previous ← used - 1#usize
          let last ← Slice.index_usize ids previous
          if last != word then do
            let written ← Slice.update ids used word
            let count ← used + 1#usize
            let b ← SketchShape.bucket_for field shape word
            let addr ← b + 1#usize
            let old ← Slice.index_usize offsets addr
            let bumped ← old + 1#u64
            let next ← Slice.update offsets addr bumped
            .ok (.cont (advanced, next, written, count))
          else .ok (.cont (advanced, offsets, ids, used))
      else .ok (.cont (advanced, offsets, ids, used)) :
        Result (ControlFlow (core.ops.range.Range Usize × Slice U64 × Slice U64 × Usize) (Slice U64 × Slice U64))) := by
    simp only [normalize_loop1.body, nextCall, bind_ok]
    rfl
  have appendAction : (do
      let written ← Slice.update ids used id
      let count ← used + 1#usize
      let b ← SketchShape.bucket_for field shape id
      let addr ← b + 1#usize
      let old ← Slice.index_usize offsets addr
      let bumped ← old + 1#u64
      let next ← Slice.update offsets addr bumped
      .ok (.cont (advanced, next, written, count)) :
        Result (ControlFlow (core.ops.range.Range Usize × Slice U64 × Slice U64 × Usize) (Slice U64 × Slice U64))) =
      .ok (.cont (advanced, inserted.offsets, inserted.ids, usizeWord (used.val + 1))) := by
    rw [wrote, bind_ok, usedPlus, bind_ok, route, bind_ok, slotPlus, bind_ok, offsetRead, bind_ok,
      tally, bind_ok, update, bind_ok]
    rfl
  by_cases zero : id = 0#u64
  · have skipped : compactAt shape.capacities.length cursor.start.val state = state := by
      change (if id = 0#u64 ∨ (used.val ≠ 0 ∧ ids[used.val - 1]! = id) then state else inserted) = _
      rw [ite_eq_left (Or.inl zero)]
    rw [skipped]
    refine ⟨advanced, used, ?_, nextStart, nextEnd, rfl, rfl, nextStart ▸ skipFrame⟩
    rw [basic, read, bind_ok]
    simp [zero, state]
  · have live : (id != 0#u64) = true := by simp [zero]
    by_cases empty : used = 0#usize
    · have zeroUsed : used.val = 0 := by rw [empty]; exact Usize.ofNatCore_val_eq _
      have model : compactAt shape.capacities.length cursor.start.val state = inserted := by
        change (if id = 0#u64 ∨ (used.val ≠ 0 ∧ ids[used.val - 1]! = id) then state else inserted) = _
        simp [zero, zeroUsed]
      rw [model]
      refine ⟨advanced, usizeWord (used.val + 1), ?_, nextStart, nextEnd,
        word_val _ usedFits, Slice.setAtNat_length _ _ _, nextStart ▸ appendFrame⟩
      rw [basic, read, bind_ok, ite_eq_left live, ite_eq_left empty]
      exact appendAction
    · have positive : 0 < used.val := by
        apply Nat.pos_of_ne_zero
        intro z
        exact empty (UScalar.eq_of_val_eq z)
      have prevCall := usize_sub_one used positive
      have prevVal : (usizeWord (used.val - 1)).val = used.val - 1 :=
        word_val _ ((Nat.sub_le ..).trans (usize_val_max used))
      have prevRead := DenseDivRem.read_normal ids (usizeWord (used.val - 1)) (by rw [prevVal]; omega)
      rw [prevVal] at prevRead
      by_cases same : ids[used.val - 1]! = id
      · have model : compactAt shape.capacities.length cursor.start.val state = state := by
          change (if id = 0#u64 ∨ (used.val ≠ 0 ∧ ids[used.val - 1]! = id) then state else inserted) = _
          rw [ite_eq_left (Or.inr ⟨Nat.ne_of_gt positive, same⟩)]
        rw [model]
        refine ⟨advanced, used, ?_, nextStart, nextEnd, rfl, rfl, nextStart ▸ skipFrame⟩
        rw [basic, read, bind_ok, ite_eq_left live, ite_eq_right empty, prevCall, bind_ok, prevRead, bind_ok]
        simp [same, state]
      · have model : compactAt shape.capacities.length cursor.start.val state = inserted := by
          change (if id = 0#u64 ∨ (used.val ≠ 0 ∧ ids[used.val - 1]! = id) then state else inserted) = _
          rw [ite_eq_right (fun h => h.elim zero (fun duplicate => same duplicate.2))]
        rw [model]
        refine ⟨advanced, usizeWord (used.val + 1), ?_, nextStart, nextEnd, word_val _ usedFits,
          Slice.setAtNat_length _ _ _, nextStart ▸ appendFrame⟩
        rw [basic, read, bind_ok, ite_eq_left live, ite_eq_right empty, prevCall, bind_ok, prevRead, bind_ok]
        have different : (ids[used.val - 1]! != id) = true := bne_iff_ne.mpr same
        rw [ite_eq_left different]
        exact appendAction

def compactFrom (buckets : Nat) : Nat → Nat → CompactState → CompactState
  | 0, _, state => state
  | fuel + 1, index, state =>
    compactFrom buckets fuel (index + 1) (compactAt buckets index state)

/-- Exact stock-generated compaction and bucket histogram loop. The invariant
bounds all source accesses, counters and writes through exhaustion. -/
def ActualNativeCandidateCompact : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (cursor : core.ops.range.Range Usize) (offsets ids : Slice U64) (used : Usize),
    cursor.start.val ≤ cursor.end.val → cursor.end.val ≤ ids.length →
    CompactBounds shape.capacities.length cursor.start.val ⟨offsets, ids, used.val⟩ →
    let state := compactFrom shape.capacities.length (cursor.end.val - cursor.start.val)
      cursor.start.val ⟨offsets, ids, used.val⟩
    normalize_loop1 field cursor shape offsets ids used = .ok (state.offsets, state.ids) ∧
    CompactBounds shape.capacities.length cursor.end.val state

theorem native_candidate_compact : ActualNativeCandidateCompact := by
  intro F field shape cursor offsets ids used ordered size bounds
  suffices ∀ fuel (cursor : core.ops.range.Range Usize) (offsets ids : Slice U64) (used : Usize),
      cursor.end.val - cursor.start.val = fuel →
      cursor.start.val ≤ cursor.end.val → cursor.end.val ≤ ids.length →
      CompactBounds shape.capacities.length cursor.start.val ⟨offsets, ids, used.val⟩ →
      let state := compactFrom shape.capacities.length fuel cursor.start.val ⟨offsets, ids, used.val⟩
      normalize_loop1 field cursor shape offsets ids used = .ok (state.offsets, state.ids) ∧
      CompactBounds shape.capacities.length cursor.end.val state from
    this _ cursor offsets ids used rfl ordered size bounds
  intro fuel
  induction fuel with
  | zero =>
    intro cursor offsets ids used exhausted ordered size bounds
    have endEq : cursor.start.val = cursor.end.val := by omega
    obtain ⟨⟨item, unchanged⟩, next, none, _⟩ :=
      RawMulTable.normal_of_spec _ _ (core.iter.range.IteratorRange.next_Usize_none_spec cursor (by omega))
    rw [none] at next
    have stop : normalize_loop1.body field shape cursor offsets ids used = .ok (.done (offsets, ids)) := by
      simp only [normalize_loop1.body, next, bind_ok]
      rfl
    refine ⟨?_, ?_⟩
    · unfold normalize_loop1 loop
      dsimp only
      rw [stop, bind_ok]
      rfl
    · simpa only [compactFrom, endEq] using bounds
  | succ fuel ih =>
    intro cursor offsets ids used remaining ordered size bounds
    have active : cursor.start.val < cursor.end.val := by omega
    obtain ⟨advanced, nextUsed, step, nextStart, nextEnd, nextVal, nextSize, nextBounds⟩ :=
      native_compact_step field shape cursor offsets ids used active size bounds
    let next := compactAt shape.capacities.length cursor.start.val ⟨offsets, ids, used.val⟩
    have fits : advanced.end.val - advanced.start.val = fuel := by rw [nextStart, nextEnd]; omega
    have nextAdmitted : CompactBounds shape.capacities.length advanced.start.val
        ⟨next.offsets, next.ids, nextUsed.val⟩ := by
      rw [nextVal]
      exact nextBounds
    obtain ⟨rest, finalBounds⟩ := ih advanced next.offsets next.ids nextUsed fits
      (by rw [nextStart, nextEnd]; omega) (by rw [nextSize, nextEnd]; exact size) nextAdmitted
    rw [nextStart, nextVal] at rest finalBounds
    rw [nextEnd] at finalBounds
    refine ⟨?_, ?_⟩
    · unfold normalize_loop1 loop
      dsimp only
      rw [step, bind_ok]
      exact rest
    · exact finalBounds

theorem compact_at_bounds (buckets index : Nat) (state : CompactState)
    (active : index < state.ids.length) (bounds : CompactBounds buckets index state) :
    CompactBounds buckets (index + 1) (compactAt buckets index state) := by
  unfold compactAt
  dsimp only
  split
  · exact skipped_bounds buckets index state bounds active
  · exact inserted_bounds buckets index state _ bounds active

#print axioms native_compact_step
#print axioms native_candidate_compact

end BulksketchBridge.CandidateNormalization
