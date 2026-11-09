import BulksketchBridge.AvxInsertionBasesPowerCells

namespace BulksketchBridge.AvxInsertionBases

open Aeneas.Std Algebra.Gf64
open ClosedLeafAdvance (usizeWord word_val)
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

noncomputable def sixContribution (c p : Nat) (v bit : Usize) : Field :=
  if bit.val < 54 ∧ v &&& bitMask (route bit).2.1 ≠ 0#usize ∧ c = (route bit).1.val ∧ 1 ≤ v.val ∧ v.val < (route bit).2.2.val ∧ p < 7
    then toField (squareTimes (bitColumn bit) (p + 1)).bv else 0

theorem bit_step_six_field (tables : Tables) (bit : Usize) (c p : Nat) (v : Usize) (room : bit.val < 64) :
    toField (cell (bitStep tables bit).1 c v.val p).bv =
      toField (cell tables.1 c v.val p).bv + sixContribution c p v bit := by
  unfold bitStep sixContribution
  rw [power_fold_six_frame tables bit 0#usize (bitColumn bit) 7 c p v room (by simp)]
  simp only [show (0#usize).val = 0 by simp, Nat.zero_le, Nat.sub_zero, true_and]
  split
  · exact toField_xor _ _
  · rw [add_zero]

/-- Every word of the completed bank is its initial value plus the sum
of exactly the processed Frobenius columns that selected that coordinate. -/
theorem bit_fold_six_field (tables : Tables) (bit : Usize) (remaining : Nat) (c p : Nat) (v : Usize)
    (cursor : bit.val + remaining = 64) :
    toField (cell (bitFold tables bit remaining).1 c v.val p).bv =
      toField (cell tables.1 c v.val p).bv +
        ∑ j ∈ Finset.range remaining, sixContribution c p v (usizeWord (bit.val + j)) := by
  induction remaining generalizing tables bit with
  | zero => simp [bitFold]
  | succ remaining ih =>
    have room : bit.val < 64 := by omega
    have step := bit_step_six_field tables bit c p v room
    have advanced := (advance_normal bit (by have := small_usize; omega)).2
    change toField (cell (bitFold (bitStep tables bit) (advance bit) remaining).1 c v.val p).bv = _
    rw [ih (bitStep tables bit) (advance bit) (by omega), step, Finset.sum_range_succ', Nat.add_zero]
    have same : usizeWord bit.val = bit :=
      UScalar.eq_of_val_eq (word_val _ (by have := small_usize; omega))
    rw [same, advanced]
    have sums : (∑ j ∈ Finset.range remaining, sixContribution c p v (usizeWord (bit.val + 1 + j))) =
        ∑ j ∈ Finset.range remaining, sixContribution c p v (usizeWord (bit.val + (j + 1))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show bit.val + 1 + j = bit.val + (j + 1) by omega]
    rw [sums]
    ac_rfl

noncomputable def fiveContribution (c p : Nat) (v bit : Usize) : Field :=
  if 54 ≤ bit.val ∧ v &&& bitMask (route bit).2.1 ≠ 0#usize ∧ c = (route bit).1.val ∧ 1 ≤ v.val ∧ v.val < (route bit).2.2.val ∧ p < 7
    then toField (squareTimes (bitColumn bit) (p + 1)).bv else 0

theorem bit_step_five_field (tables : Tables) (bit : Usize) (c p : Nat) (v : Usize) (room : bit.val < 64) :
    toField (cell (bitStep tables bit).2 c v.val p).bv =
      toField (cell tables.2 c v.val p).bv + fiveContribution c p v bit := by
  unfold bitStep fiveContribution
  rw [power_fold_five_frame tables bit 0#usize (bitColumn bit) 7 c p v room (by simp)]
  simp only [show (0#usize).val = 0 by simp, Nat.zero_le, Nat.sub_zero, true_and]
  split
  · exact toField_xor _ _
  · rw [add_zero]

/-- Every word of the completed bank is its initial value plus the sum
of exactly the processed Frobenius columns that selected that coordinate. -/
theorem bit_fold_five_field (tables : Tables) (bit : Usize) (remaining : Nat) (c p : Nat) (v : Usize)
    (cursor : bit.val + remaining = 64) :
    toField (cell (bitFold tables bit remaining).2 c v.val p).bv =
      toField (cell tables.2 c v.val p).bv +
        ∑ j ∈ Finset.range remaining, fiveContribution c p v (usizeWord (bit.val + j)) := by
  induction remaining generalizing tables bit with
  | zero => simp [bitFold]
  | succ remaining ih =>
    have room : bit.val < 64 := by omega
    have step := bit_step_five_field tables bit c p v room
    have advanced := (advance_normal bit (by have := small_usize; omega)).2
    change toField (cell (bitFold (bitStep tables bit) (advance bit) remaining).2 c v.val p).bv = _
    rw [ih (bitStep tables bit) (advance bit) (by omega), step, Finset.sum_range_succ', Nat.add_zero]
    have same : usizeWord bit.val = bit :=
      UScalar.eq_of_val_eq (word_val _ (by have := small_usize; omega))
    rw [same, advanced]
    have sums : (∑ j ∈ Finset.range remaining, fiveContribution c p v (usizeWord (bit.val + 1 + j))) =
        ∑ j ∈ Finset.range remaining, fiveContribution c p v (usizeWord (bit.val + (j + 1))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show bit.val + 1 + j = bit.val + (j + 1) by omega]
    rw [sums]
    ac_rfl

end BulksketchBridge.AvxInsertionBases
