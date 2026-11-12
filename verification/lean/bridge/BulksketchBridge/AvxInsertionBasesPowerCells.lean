import BulksketchBridge.AvxInsertionBases
import BulksketchBridge.AvxInsertionBasesCells

namespace BulksketchBridge.AvxInsertionBases

open Aeneas.Std Algebra.Gf64

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

def squareTimes (column : U64) : Nat → U64
  | 0 => column
  | power + 1 => squareTimes (squareColumn column) power

theorem square_times_field (column : U64) (power : Nat) :
    toField (squareTimes column power).bv = toField column.bv ^ (2 ^ power) := by
  induction power generalizing column with
  | zero => simp [squareTimes]
  | succ power ih =>
    rw [squareTimes, ih, square_column_field, ← pow_mul, pow_succ]
    rw [Nat.mul_comm]


theorem power_step_six_frame (tables : Tables) (bit power : Usize) (column : U64) (c p : Nat) (v : Usize)
    (bitRoom : bit.val < 64) (powerRoom : power.val < 7) :
    cell (powerStep tables bit power column).1 c v.val p =
      if bit.val < 54 ∧ v &&& bitMask (route bit).2.1 ≠ 0#usize ∧ c = (route bit).1.val ∧ p = power.val ∧ 1 ≤ v.val ∧ v.val < (route bit).2.2.val
      then cell tables.1 c v.val p ^^^ squareColumn column else cell tables.1 c v.val p := by
  have count := route_count bit
  have cursor : (1#usize).val + ((route bit).2.2.val - 1) = (route bit).2.2.val := by
    change 1 + ((route bit).2.2.val - 1) = _
    omega
  simpa only [powerStep, show (1#usize).val = 1 by simp] using
    value_fold_six_frame tables bit (squareColumn column) power (route bit).1 (route bit).2.1
      (route bit).2.2 1#usize ((route bit).2.2.val - 1) c p v
      (route_bounds bit power bitRoom powerRoom) cursor

theorem power_fold_six_frame (tables : Tables) (bit power : Usize) (column : U64) (remaining : Nat)
    (c p : Nat) (v : Usize) (bitRoom : bit.val < 64) (cursor : power.val + remaining = 7) :
    cell (powerFold bit tables column power remaining).1 c v.val p =
      if bit.val < 54 ∧ v &&& bitMask (route bit).2.1 ≠ 0#usize ∧ c = (route bit).1.val ∧ 1 ≤ v.val ∧ v.val < (route bit).2.2.val ∧ power.val ≤ p ∧ p < 7
      then cell tables.1 c v.val p ^^^ squareTimes column (p - power.val + 1)
      else cell tables.1 c v.val p := by
  induction remaining generalizing tables power column with
  | zero =>
    have none : ¬ (power.val ≤ p ∧ p < 7) := by omega
    simp [powerFold, none]
  | succ remaining ih =>
    have active : power.val < 7 := by omega
    have advanced := (advance_normal power (by have := small_usize; omega)).2
    let updated := powerStep tables bit power column
    have step := power_step_six_frame tables bit power column c p v bitRoom active
    change cell (powerFold bit updated (squareColumn column) (advance power) remaining).1 c v.val p = _
    rw [ih updated (advance power) (squareColumn column) (by omega)]
    by_cases here : p = power.val
    · subst p
      have noLater : ¬ (advance power).val ≤ power.val := by omega
      simp only [noLater, and_false, ite_false, updated, step, Nat.le_refl, active, and_true, true_and, Nat.sub_self]
      rfl
    · have stable : cell updated.1 c v.val p = cell tables.1 c v.val p := by
        simp only [updated, step, here, false_and, and_false, ite_false]
      have lower : (advance power).val ≤ p ↔ power.val ≤ p := by omega
      simp only [stable, lower]
      split
      · rename_i inside
        have past : power.val ≤ p := inside.2.2.2.2.2.1
        rw [show p - (advance power).val + 1 = p - power.val by omega]
        rfl
      · rfl

theorem power_step_five_frame (tables : Tables) (bit power : Usize) (column : U64) (c p : Nat) (v : Usize)
    (bitRoom : bit.val < 64) (powerRoom : power.val < 7) :
    cell (powerStep tables bit power column).2 c v.val p =
      if 54 ≤ bit.val ∧ v &&& bitMask (route bit).2.1 ≠ 0#usize ∧ c = (route bit).1.val ∧ p = power.val ∧ 1 ≤ v.val ∧ v.val < (route bit).2.2.val
      then cell tables.2 c v.val p ^^^ squareColumn column else cell tables.2 c v.val p := by
  have count := route_count bit
  have cursor : (1#usize).val + ((route bit).2.2.val - 1) = (route bit).2.2.val := by
    change 1 + ((route bit).2.2.val - 1) = _
    omega
  simpa only [powerStep, show (1#usize).val = 1 by simp] using
    value_fold_five_frame tables bit (squareColumn column) power (route bit).1 (route bit).2.1
      (route bit).2.2 1#usize ((route bit).2.2.val - 1) c p v
      (route_bounds bit power bitRoom powerRoom) cursor

theorem power_fold_five_frame (tables : Tables) (bit power : Usize) (column : U64) (remaining : Nat)
    (c p : Nat) (v : Usize) (bitRoom : bit.val < 64) (cursor : power.val + remaining = 7) :
    cell (powerFold bit tables column power remaining).2 c v.val p =
      if 54 ≤ bit.val ∧ v &&& bitMask (route bit).2.1 ≠ 0#usize ∧ c = (route bit).1.val ∧ 1 ≤ v.val ∧ v.val < (route bit).2.2.val ∧ power.val ≤ p ∧ p < 7
      then cell tables.2 c v.val p ^^^ squareTimes column (p - power.val + 1)
      else cell tables.2 c v.val p := by
  induction remaining generalizing tables power column with
  | zero =>
    have none : ¬ (power.val ≤ p ∧ p < 7) := by omega
    simp [powerFold, none]
  | succ remaining ih =>
    have active : power.val < 7 := by omega
    have advanced := (advance_normal power (by have := small_usize; omega)).2
    let updated := powerStep tables bit power column
    have step := power_step_five_frame tables bit power column c p v bitRoom active
    change cell (powerFold bit updated (squareColumn column) (advance power) remaining).2 c v.val p = _
    rw [ih updated (advance power) (squareColumn column) (by omega)]
    by_cases here : p = power.val
    · subst p
      have noLater : ¬ (advance power).val ≤ power.val := by omega
      simp only [noLater, and_false, ite_false, updated, step, Nat.le_refl, active, and_true, true_and, Nat.sub_self]
      rfl
    · have stable : cell updated.2 c v.val p = cell tables.2 c v.val p := by
        simp only [updated, step, here, false_and, and_false, ite_false]
      have lower : (advance power).val ≤ p ↔ power.val ≤ p := by omega
      simp only [stable, lower]
      split
      · rename_i inside
        have past : power.val ≤ p := inside.2.2.2.2.2.1
        rw [show p - (advance power).val + 1 = p - power.val by omega]
        rfl
      · rfl

end BulksketchBridge.AvxInsertionBases
