import BulksketchBridge.AvxInsertionBasesInner

namespace BulksketchBridge.AvxInsertionBases

open Aeneas.Std FrobeniusTables

set_option maxRecDepth 4096

/-- Exact frame of a nested mutable array write. The updated word is the
old cell XOR the supplied Frobenius column. -/
theorem xor_cell_frame {chunks values : Usize} (table : Table chunks values)
    (chunk value power : Usize) (column : U64) (c v p : Nat)
    (chunkRoom : chunk.val < chunks.val) (valueRoom : value.val < values.val) (powerRoom : power.val < 8) :
    cell (xorCell table chunk value power column) c v p =
      if c = chunk.val ∧ v = value.val ∧ p = power.val then cell table c v p ^^^ column
      else cell table c v p := by
  unfold xorCell cell
  by_cases sameChunk : c = chunk.val
  · subst c
    rw [entry_set_same _ _ _ chunkRoom]
    by_cases sameValue : v = value.val
    · subst v
      rw [entry_set_same _ _ _ valueRoom]
      by_cases samePower : p = power.val
      · subst p
        rw [entry_set_same _ _ _ (by exact powerRoom)]
        simp
      · rw [entry_set_other _ _ _ _ (Ne.symm samePower)]
        simp [samePower]
    · rw [entry_set_other _ _ _ _ (Ne.symm sameValue)]
      simp [sameValue]
  · rw [entry_set_other _ _ _ _ (Ne.symm sameChunk)]
    simp [sameChunk]

theorem value_step_six_frame (tables : Tables) (bit : Usize) (column : U64)
    (power chunk shift value : Usize) (c v p : Nat)
    (chunkRoom : chunk.val < 9) (valueRoom : value.val < 64) (powerRoom : power.val < 7) :
    cell (valueStep tables bit column power chunk shift value).1 c v p =
      if bit.val < 54 ∧ value &&& bitMask shift ≠ 0#usize ∧
          c = chunk.val ∧ v = value.val ∧ p = power.val
      then cell tables.1 c v p ^^^ column else cell tables.1 c v p := by
  unfold valueStep
  by_cases mask : value &&& bitMask shift = 0#usize
  · simp [mask]
  · by_cases first : bit.val < 54
    · simp only [mask, first, not_false_eq_true, ne_eq, ite_true, true_and]
      exact xor_cell_frame tables.1 chunk value power column c v p chunkRoom valueRoom (by omega)
    · simp [mask, first]

theorem value_step_five_frame (tables : Tables) (bit : Usize) (column : U64)
    (power chunk shift value : Usize) (c v p : Nat)
    (chunkRoom : chunk.val < 2) (valueRoom : value.val < 32) (powerRoom : power.val < 7) :
    cell (valueStep tables bit column power chunk shift value).2 c v p =
      if 54 ≤ bit.val ∧ value &&& bitMask shift ≠ 0#usize ∧
          c = chunk.val ∧ v = value.val ∧ p = power.val
      then cell tables.2 c v p ^^^ column else cell tables.2 c v p := by
  unfold valueStep
  by_cases mask : value &&& bitMask shift = 0#usize
  · simp [mask]
  · by_cases first : bit.val < 54
    · simp [mask, first, show ¬54 ≤ bit.val by omega]
    · simp only [mask, first, not_false_eq_true, ne_eq, ite_true,
        show 54 ≤ bit.val by omega, true_and]
      exact xor_cell_frame tables.2 chunk value power column c v p chunkRoom valueRoom (by omega)


/-- The whole value scan changes exactly one selected coordinate, with
the other coordinates preserved. -/
theorem value_fold_six_frame (tables : Tables) (bit : Usize) (column : U64)
    (power chunk shift count cursor : Usize) (remaining : Nat) (c p : Nat) (v : Usize)
    (bounds : ValueBounds bit power chunk shift count) (range : cursor.val + remaining = count.val) :
    cell (valueFold bit column power chunk shift tables cursor remaining).1 c v.val p =
      if bit.val < 54 ∧ v &&& bitMask shift ≠ 0#usize ∧ c = chunk.val ∧ p = power.val ∧
        cursor.val ≤ v.val ∧ v.val < count.val
      then cell tables.1 c v.val p ^^^ column else cell tables.1 c v.val p := by
  induction remaining generalizing tables cursor with
  | zero =>
    simp only [valueFold]
    have unreachable : ¬ (cursor.val ≤ v.val ∧ v.val < count.val) := by omega
    simp [unreachable]
  | succ remaining ih =>
    have active : cursor.val < count.val := by omega
    have countRoom : count.val ≤ 64 := by
      by_cases first : bit.val < 54
      · rw [(bounds.2.2.1 first).2]
      · rw [(bounds.2.2.2 (by omega)).2]; decide
    have advanced := (advance_normal cursor (by have := small_usize; omega)).2
    let updated := valueStep tables bit column power chunk shift cursor
    have step : cell updated.1 c v.val p =
        if bit.val < 54 ∧ cursor &&& bitMask shift ≠ 0#usize ∧
            c = chunk.val ∧ v.val = cursor.val ∧ p = power.val
        then cell tables.1 c v.val p ^^^ column else cell tables.1 c v.val p := by
      by_cases selectedBank : bit.val < 54
      · obtain ⟨chunkRoom, size⟩ := bounds.2.2.1 selectedBank
        exact value_step_six_frame tables bit column power chunk shift cursor c v.val p
          chunkRoom (by omega) bounds.1
      · have branch : ¬bit.val < 54 := by omega
        by_cases mask : cursor &&& bitMask shift = 0#usize
        · simp [updated, valueStep, mask, selectedBank]
        · simp [updated, valueStep, mask, selectedBank, branch]
    change cell (valueFold bit column power chunk shift updated (advance cursor) remaining).1 c v.val p = _
    rw [ih updated (advance cursor) (by omega)]
    by_cases here : v = cursor
    · subst v
      have noLater : ¬ (advance cursor).val ≤ cursor.val := by omega
      simp only [noLater, and_false, ite_false, step, Nat.le_refl, active, and_true, true_and]
    · have different : v.val ≠ cursor.val := fun equal => here (UScalar.eq_of_val_eq equal)
      have unchanged : cell updated.1 c v.val p = cell tables.1 c v.val p := by
        simp only [step, different, false_and, and_false, ite_false]
      have sameLower : (advance cursor).val ≤ v.val ↔ cursor.val ≤ v.val := by omega
      simp only [unchanged, sameLower]

/-- The whole value scan changes exactly one selected coordinate, with
the other coordinates preserved. -/
theorem value_fold_five_frame (tables : Tables) (bit : Usize) (column : U64)
    (power chunk shift count cursor : Usize) (remaining : Nat) (c p : Nat) (v : Usize)
    (bounds : ValueBounds bit power chunk shift count) (range : cursor.val + remaining = count.val) :
    cell (valueFold bit column power chunk shift tables cursor remaining).2 c v.val p =
      if 54 ≤ bit.val ∧ v &&& bitMask shift ≠ 0#usize ∧ c = chunk.val ∧ p = power.val ∧
        cursor.val ≤ v.val ∧ v.val < count.val
      then cell tables.2 c v.val p ^^^ column else cell tables.2 c v.val p := by
  induction remaining generalizing tables cursor with
  | zero =>
    simp only [valueFold]
    have unreachable : ¬ (cursor.val ≤ v.val ∧ v.val < count.val) := by omega
    simp [unreachable]
  | succ remaining ih =>
    have active : cursor.val < count.val := by omega
    have countRoom : count.val ≤ 64 := by
      by_cases first : bit.val < 54
      · rw [(bounds.2.2.1 first).2]
      · rw [(bounds.2.2.2 (by omega)).2]; decide
    have advanced := (advance_normal cursor (by have := small_usize; omega)).2
    let updated := valueStep tables bit column power chunk shift cursor
    have step : cell updated.2 c v.val p =
        if 54 ≤ bit.val ∧ cursor &&& bitMask shift ≠ 0#usize ∧
            c = chunk.val ∧ v.val = cursor.val ∧ p = power.val
        then cell tables.2 c v.val p ^^^ column else cell tables.2 c v.val p := by
      by_cases selectedBank : 54 ≤ bit.val
      · obtain ⟨chunkRoom, size⟩ := bounds.2.2.2 selectedBank
        exact value_step_five_frame tables bit column power chunk shift cursor c v.val p
          chunkRoom (by omega) bounds.1
      · have branch : bit.val < 54 := by omega
        by_cases mask : cursor &&& bitMask shift = 0#usize
        · simp [updated, valueStep, mask, selectedBank]
        · simp [updated, valueStep, mask, selectedBank, branch]
    change cell (valueFold bit column power chunk shift updated (advance cursor) remaining).2 c v.val p = _
    rw [ih updated (advance cursor) (by omega)]
    by_cases here : v = cursor
    · subst v
      have noLater : ¬ (advance cursor).val ≤ cursor.val := by omega
      simp only [noLater, and_false, ite_false, step, Nat.le_refl, active, and_true, true_and]
    · have different : v.val ≠ cursor.val := fun equal => here (UScalar.eq_of_val_eq equal)
      have unchanged : cell updated.2 c v.val p = cell tables.2 c v.val p := by
        simp only [step, different, false_and, and_false, ite_false]
      have sameLower : (advance cursor).val ≤ v.val ↔ cursor.val ≤ v.val := by omega
      simp only [unchanged, sameLower]

end BulksketchBridge.AvxInsertionBases
