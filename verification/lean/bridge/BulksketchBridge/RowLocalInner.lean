import Arithmetic.RowLocalGenerated
import BulksketchBridge.RowLocalModel
import BulksketchBridge.DenseDivRemControl

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.sketch.candidates

structure RowCompactState where
  ids : Slice U64
  used : Nat

def rowCompactAt (base index : Nat) (state : RowCompactState) : RowCompactState :=
  let id := state.ids[index]!
  if id = 0#u64 ∨ (state.used ≠ base ∧ state.ids[state.used - 1]! = id)
  then state
  else ⟨state.ids.setAtNat state.used id, state.used + 1⟩

def rowCompactFrom (base : Nat) : Nat → Nat → RowCompactState → RowCompactState
  | 0, _, state => state
  | fuel + 1, index, state => rowCompactFrom base fuel (index + 1) (rowCompactAt base index state)

@[simp] theorem row_compact_step_length (base index : Nat) (state : RowCompactState) :
    (rowCompactAt base index state).ids.length = state.ids.length := by
  unfold rowCompactAt
  dsimp only
  split
  · rfl
  · exact Slice.setAtNat_length _ _ _

private theorem row_compact_step {base used : Usize} (cursor : core.ops.range.Range Usize)
    (ids : Slice U64) (baseBound : base.val ≤ used.val) (order : used.val ≤ cursor.start.val)
    (active : cursor.start.val < cursor.end.val) (room : cursor.end.val ≤ ids.length) :
    let state := rowCompactAt base.val cursor.start.val ⟨ids, used.val⟩
    ∃ advanced nextUsed,
      normalize_rows_loop0_loop0.body base cursor ids used = .ok (.cont (advanced, state.ids, nextUsed)) ∧
      advanced.start.val = cursor.start.val + 1 ∧ advanced.end = cursor.end ∧
      nextUsed.val = state.used ∧ base.val ≤ state.used ∧ state.used ≤ advanced.start.val := by
  dsimp only
  let value := ids[cursor.start.val]!
  let before : RowCompactState := ⟨ids, used.val⟩
  obtain ⟨⟨item, advanced⟩, step, itemVal, advanceVal, endVal⟩ :=
    RawMulTable.normal_of_spec _ _ (core.iter.range.IteratorRange.next_Usize_some_spec cursor active)
  rw [itemVal] at step
  have read : Slice.index_usize ids cursor.start = .ok value :=
    DenseDivRem.read_normal ids cursor.start (by omega)
  have max : ids.length ≤ Usize.max := ids.length_ineq
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  obtain ⟨nextUsed, bump, usedVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := used) (y := 1#usize) (by rw [one]; omega))
  rw [one] at usedVal
  have wrote := Reconstruction.update_normal ids used value (by omega)
  have at_start : used = base ↔ used.val = base.val :=
    ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩
  have unfolded : normalize_rows_loop0_loop0.body base cursor ids used =
      (if value != 0#u64 then
        if used = base then do
          let written ← Slice.update ids used value
          let count ← used + 1#usize
          .ok (.cont (advanced, written, count))
        else do
          let last ← used - 1#usize
          let old ← Slice.index_usize ids last
          if old != value then do
            let written ← Slice.update ids used value
            let count ← used + 1#usize
            .ok (.cont (advanced, written, count))
          else .ok (.cont (advanced, ids, used))
      else .ok (.cont (advanced, ids, used)) :
      Result (ControlFlow (core.ops.range.Range Usize × Slice U64 × Usize) (Slice U64 × Usize))) := by
    simp only [normalize_rows_loop0_loop0.body, step, bind_ok]
    dsimp! only
    rw [read, bind_ok]
  by_cases zero : value = 0#u64
  · have skipped : rowCompactAt base.val cursor.start.val before = before := by
      change (if value = 0#u64 ∨ _ then before else _) = _
      rw [ite_eq_left (Or.inl zero)]
    rw [skipped]
    refine ⟨advanced, used, ?_, advanceVal, endVal, rfl, baseBound, by change used.val ≤ _; omega⟩
    rw [unfolded]
    simp [zero, before]
  · have live : (value != 0#u64) = true := bne_iff_ne.mpr zero
    by_cases first : used = base
    · have stored : rowCompactAt base.val cursor.start.val before = ⟨ids.setAtNat used.val value, used.val + 1⟩ := by
        change (if value = 0#u64 ∨ (used.val ≠ base.val ∧ ids[used.val - 1]! = value)
          then before else _) = _
        have same := at_start.mp first
        rw [ite_eq_right (fun h => h.elim zero (fun d => d.1 same))]
      rw [stored]
      refine ⟨advanced, nextUsed, ?_, advanceVal, endVal, usedVal, ?_, ?_⟩
      · rw [unfolded, ite_eq_left live, ite_eq_left first, wrote, bind_ok, bump, bind_ok]
      · change base.val ≤ used.val + 1
        omega
      · change used.val + 1 ≤ _
        omega
    · have nonempty : 0 < used.val := by
        have different : used.val ≠ base.val := fun same => first (at_start.mpr same)
        omega
      obtain ⟨previous, sub, prevVal, _⟩ := RawMulTable.normal_of_spec _ _
        (Usize.sub_spec (x := used) (y := 1#usize) (by rw [one]; exact nonempty))
      rw [one] at prevVal
      have prevRead := DenseDivRem.read_normal ids previous (by rw [prevVal]; omega)
      rw [prevVal] at prevRead
      by_cases repeated : ids[used.val - 1]! = value
      · have skipped : rowCompactAt base.val cursor.start.val before = before := by
          change (if value = 0#u64 ∨ (used.val ≠ base.val ∧ ids[used.val - 1]! = value)
            then before else _) = _
          rw [ite_eq_left (Or.inr ⟨fun same => first (at_start.mpr same), repeated⟩)]
        rw [skipped]
        refine ⟨advanced, used, ?_, advanceVal, endVal, rfl, baseBound, by change used.val ≤ _; omega⟩
        rw [unfolded, ite_eq_left live, ite_eq_right first, sub, bind_ok, prevRead, bind_ok]
        have equal : ¬((ids[used.val - 1]! != value) = true) :=
          fun differs => (bne_iff_ne.mp differs) repeated
        rw [ite_eq_right equal]
      · have stored : rowCompactAt base.val cursor.start.val before = ⟨ids.setAtNat used.val value, used.val + 1⟩ := by
          change (if value = 0#u64 ∨ (used.val ≠ base.val ∧ ids[used.val - 1]! = value)
            then before else _) = _
          rw [ite_eq_right (fun h => h.elim zero (fun d => repeated d.2))]
        rw [stored]
        refine ⟨advanced, nextUsed, ?_, advanceVal, endVal, usedVal, ?_, ?_⟩
        · rw [unfolded, ite_eq_left live, ite_eq_right first, sub, bind_ok, prevRead, bind_ok,
            ite_eq_left (bne_iff_ne.mpr repeated), wrote, bind_ok, bump, bind_ok]
        · change base.val ≤ used.val + 1
          omega
        · change used.val + 1 ≤ _
          omega

/-- Exact mutable source compaction for one sorted row, including its
row-relative first accepted word and preserved output count bounds. -/
def ActualNativeRowLocalCompact : Prop :=
  ∀ (base : Usize) (cursor : core.ops.range.Range Usize) (ids : Slice U64) (used : Usize),
    base.val ≤ used.val → used.val ≤ cursor.start.val → cursor.start.val ≤ cursor.end.val →
    cursor.end.val ≤ ids.length →
    let state := rowCompactFrom base.val (cursor.end.val - cursor.start.val) cursor.start.val ⟨ids, used.val⟩
    ∃ finalUsed,
      normalize_rows_loop0_loop0 cursor ids used base = .ok (state.ids, finalUsed) ∧
      finalUsed.val = state.used ∧ state.ids.length = ids.length ∧ base.val ≤ state.used ∧ state.used ≤ cursor.end.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem native_row_local_compact : ActualNativeRowLocalCompact := by
  intro base cursor ids used baseRoom usedRoom order room
  suffices ∀ fuel (cursor : core.ops.range.Range Usize) (ids : Slice U64) (used : Usize),
    cursor.end.val - cursor.start.val = fuel →
    base.val ≤ used.val → used.val ≤ cursor.start.val → cursor.start.val ≤ cursor.end.val →
    cursor.end.val ≤ ids.length →
    let state := rowCompactFrom base.val fuel cursor.start.val ⟨ids, used.val⟩
    ∃ finalUsed,
      normalize_rows_loop0_loop0 cursor ids used base = .ok (state.ids, finalUsed) ∧
      finalUsed.val = state.used ∧ state.ids.length = ids.length ∧ base.val ≤ state.used ∧ state.used ≤ cursor.end.val
    from this _ cursor ids used rfl baseRoom usedRoom order room
  intro fuel
  induction fuel with
  | zero =>
    intro cursor ids used exhausted baseRoom usedRoom order room
    obtain ⟨⟨item, unchanged⟩, next, noMore, _⟩ := RawMulTable.normal_of_spec _ _
      (core.iter.range.IteratorRange.next_Usize_none_spec cursor (by omega))
    rw [noMore] at next
    have stop : normalize_rows_loop0_loop0.body base cursor ids used = .ok (.done (ids, used)) := by
      simp only [normalize_rows_loop0_loop0.body, next, bind_ok]
      rfl
    refine ⟨used, ?_, rfl, rfl, baseRoom, usedRoom.trans order⟩
    unfold normalize_rows_loop0_loop0 loop
    dsimp only
    rw [stop, bind_ok]
    rfl
  | succ fuel ih =>
    intro cursor ids used remaining baseRoom usedRoom order room
    have active : cursor.start.val < cursor.end.val := by omega
    obtain ⟨advanced, nextUsed, step, advanceVal, endVal, usedVal, baseBound, usedBound⟩ :=
      row_compact_step (base := base) (used := used) cursor ids baseRoom usedRoom active room
    let next := rowCompactAt base.val cursor.start.val ⟨ids, used.val⟩
    have nextLen : next.ids.length = ids.length := row_compact_step_length _ _ _
    obtain ⟨finalUsed, normal, modelUsed, finalLen, finalBase, finalEnd⟩ :=
      ih advanced next.ids nextUsed (by rw [advanceVal, endVal]; omega)
        (by rw [usedVal]; exact baseBound) (by rw [usedVal]; exact usedBound)
        (by rw [advanceVal, endVal]; omega) (by rw [endVal, nextLen]; exact room)
    rw [advanceVal, usedVal] at normal modelUsed finalLen finalBase finalEnd
    rw [endVal] at finalEnd
    refine ⟨finalUsed, ?_, modelUsed, finalLen.trans nextLen, finalBase, finalEnd⟩
    unfold normalize_rows_loop0_loop0 loop
    dsimp only
    rw [step, bind_ok]
    exact normal

#print axioms native_row_local_compact

end BulksketchBridge.CandidateNormalization
