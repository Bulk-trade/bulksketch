import BulksketchBridge.AffineSubspaces

namespace BulksketchBridge.AffineSubspaces

open Aeneas Aeneas.Std
open AffineLinearEval Algebra.Gf64 RebuiltLfsr
open bulksketch.backend.contract

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

private theorem product_field (left right : U64) :
    toField (productWord left right).bv = toField left.bv * toField right.bv :=
  toField_mul _ _

private theorem square_field (value : U64) :
    toField (Square.expectedWord value).bv = toField value.bv ^ 2 :=
  toField_square _

private theorem get_written (words : Slice U64) (index : Nat) (value : U64)
    (bound : index < words.length) : (words.setAtNat index value)[index]! = value := by
  simpa only [Slice.getElem!_Nat_eq] using Slice.getElem!_Nat_setAtNat_eq words index value bound

private theorem get_untouched (words : Slice U64) (index position : Nat) (value : U64)
    (apart : index ≠ position) : (words.setAtNat index value)[position]! = words[position]! := by
  simpa only [Slice.getElem!_Nat_eq] using Slice.getElem!_Nat_setAtNat_ne words index position value apart

private theorem innerStep_field (output : Slice U64) (direction coefficient : U64)
    (index position : Nat) (room : index + 1 < output.length) :
    toField (innerStep output direction coefficient index)[position]!.bv =
      toField output[position]!.bv +
        (if position = index then toField direction.bv * toField coefficient.bv else 0) +
        (if position = index + 1 then toField coefficient.bv ^ 2 else 0) := by
  let next := output.setAtNat index (output[index]! ^^^ productWord direction coefficient)
  have nextLength : next.length = output.length := Slice.setAtNat_length _ _ _
  have written : index < output.length := by omega
  change toField (next.setAtNat (index + 1) (next[index + 1]! ^^^ Square.expectedWord coefficient))[position]!.bv = _
  by_cases same : position = index
  · subst position
    rw [get_untouched _ _ _ _ (by omega)]
    have read : next[index]! = output[index]! ^^^ productWord direction coefficient :=
      get_written _ _ _ written
    rw [read]
    simp only [ite_true, show index ≠ index + 1 by omega, ite_false, add_zero]
    change toField (output[index]!.bv ^^^ (productWord direction coefficient).bv) = _
    rw [toField_xor, product_field]
  · by_cases adjacent : position = index + 1
    · subst position
      rw [get_written _ _ _ (by rw [nextLength]; exact room)]
      have read : next[index + 1]! = output[index + 1]! := get_untouched _ _ _ _ (by omega)
      rw [read]
      simp only [same, ite_false, ite_true, add_zero]
      change toField (output[index + 1]!.bv ^^^ (Square.expectedWord coefficient).bv) = _
      rw [toField_xor, square_field]
    · rw [get_untouched _ _ _ _ (Ne.symm adjacent)]
      have read : next[position]! = output[position]! := get_untouched _ _ _ _ (Ne.symm same)
      simp only [read, same, adjacent, ite_false, add_zero]

theorem innerFold_field (previous output : Slice U64) (direction : U64)
    (index count position : Nat) (room : index + count < output.length) :
    toField (innerFold previous direction output index count)[position]!.bv =
      toField output[position]!.bv +
        (if index ≤ position ∧ position < index + count
          then toField direction.bv * toField previous[position]!.bv else 0) +
        (if index < position ∧ position ≤ index + count
          then toField previous[position - 1]!.bv ^ 2 else 0) := by
  induction count generalizing index output with
  | zero =>
    simp only [innerFold, show ¬ (index ≤ position ∧ position < index) by omega,
      show ¬ (index < position ∧ position ≤ index) by omega, ite_false, add_zero]
  | succ count ih =>
    rw [innerFold, ih _ _ (by rw [innerStep_length]; omega), innerStep_field _ _ _ _ _ (by omega)]
    by_cases same : position = index
    · subst position
      simp only [ite_true, show index ≠ index + 1 by omega, ite_false, add_zero,
        show ¬ (index + 1 ≤ index ∧ index < index + 1 + count) by omega,
        show ¬ (index + 1 < index ∧ index ≤ index + 1 + count) by omega,
        show index ≤ index ∧ index < index + (count + 1) by omega,
        show ¬ (index < index ∧ index ≤ index + (count + 1)) by omega, true_and, ite_true]
    · by_cases adjacent : position = index + 1
      · subst position
        simp only [same, ite_false, ite_true, add_zero,
          show ¬ (index + 1 < index + 1 ∧ index + 1 ≤ index + 1 + count) by omega,
          show index < index + 1 ∧ index + 1 ≤ index + (count + 1) by omega,
          show index + 1 - 1 = index by omega,
          show (index ≤ index + 1 ∧ index + 1 < index + (count + 1)) ↔
            (index + 1 ≤ index + 1 ∧ index + 1 < index + 1 + count) by omega, true_and, ite_true]
        ring
      · simp only [same, adjacent, ite_false, add_zero,
          show (index ≤ position ∧ position < index + (count + 1)) ↔
            (index + 1 ≤ position ∧ position < index + 1 + count) by omega,
          show (index < position ∧ position ≤ index + (count + 1)) ↔
            (index + 1 < position ∧ position ≤ index + 1 + count) by omega]

/-- At coefficient i, scaling contributes the previous coefficient at i and
squaring contributes the previous coefficient at i-1. Both terms are zero
when their source index does not exist. -/
theorem nextRow_coefficients (previous shape : Slice U64) (direction : U64)
    (position : Nat) (bounded : position < shape.length)
    (room : previous.length < shape.length) :
    toField (nextRow previous shape direction)[position]!.bv =
      (if position < previous.length
        then toField direction.bv * toField previous[position]!.bv else 0) +
      (if 0 < position ∧ position ≤ previous.length
        then toField previous[position - 1]!.bv ^ 2 else 0) := by
  have zeroWord : (zeroWords shape)[position]! = 0#u64 := by
    simp only [Slice.getElem!_Nat_eq, zeroWords, Slice.from_val]
    rw [← List.Inhabited_getElem_eq_getElem! _ _ (by simpa using bounded), List.getElem_replicate]
  unfold nextRow
  rw [innerFold_field _ _ _ _ _ _ (by rw [zero_length]; omega), zeroWord]
  simp only [show toField (0#u64).bv = 0 from toField_zero, Nat.zero_le, true_and, zero_add]

theorem row_length (table : Slice U64) (rank : Nat) (room : offset (rank + 1) ≤ table.length) :
    (row table rank).length = rank + 1 := by
  unfold row
  rw [ClosedLeaf.region_length _ _ _ room, offset_succ]
  omega

theorem row_read (table : Slice U64) (rank position : Nat)
    (room : offset (rank + 1) ≤ table.length) (bounded : position < rank + 1) :
    (row table rank)[position]! = table[offset rank + position]! := by
  simp only [row, ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
  exact List.getElem!_slice (offset rank) (offset (rank + 1)) position table.val
    ⟨room, by rw [offset_succ]; omega⟩

/-- A successful original-table step has the intended quotient-field
coefficients and leaves all words outside its next row unchanged. -/
theorem tableStep_coefficients {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (table updated : Slice U64) (rank : Nat)
    (direction : U64) (room : offset (rank + 1 + 1) ≤ table.length)
    (ran : tableStep kernels table rank direction = .ok updated) :
    updated.length = table.length ∧
    (∀ position, position < rank + 2 →
      toField (row updated (rank + 1))[position]!.bv =
        (if position < rank + 1 then
          linearValueFrom (row table rank) direction 0 * toField (row table rank)[position]!.bv else 0) +
        (if 0 < position ∧ position ≤ rank + 1
          then toField (row table rank)[position - 1]!.bv ^ 2 else 0)) ∧
    (∀ position, position < offset (rank + 1) ∨ offset (rank + 1 + 1) ≤ position →
      updated[position]! = table[position]!) := by
  have previousRoom : offset (rank + 1) ≤ table.length := (offset_mono (by omega)).trans room
  have previousSize := row_length table rank previousRoom
  have shapeSize := row_length table (rank + 1) room
  obtain ⟨directionValue, evaluated, meaning⟩ :=
    linear_eval_refines kernels (row table rank) direction arithmetic
  let replacement := nextRow (row table rank) (row table (rank + 1)) directionValue
  have replacementSize : replacement.length = rank + 2 := by
    rw [show replacement.length = (nextRow _ _ _).length by rfl, nextRow_length, shapeSize]
  have exactOutput : updated = table.setSlice! (offset (rank + 1)) replacement.val := by
    simpa only [tableStep, evaluated, bind_ok, Result.ok.injEq, replacement, eq_comm] using ran
  have sameLength : updated.length = table.length := by rw [exactOutput, Slice.setSlice!_length]
  refine ⟨sameLength, ?_, ?_⟩
  · intro position bounded
    rw [row_read updated (rank + 1) position (by rwa [sameLength]) bounded, exactOutput]
    have written := Slice.setSlice!_getElem!_middle table replacement.val (offset (rank + 1))
      (offset (rank + 1) + position) (by
        have ending := offset_succ (rank + 1)
        change offset (rank + 1) ≤ offset (rank + 1) + position ∧
          offset (rank + 1) + position - offset (rank + 1) < replacement.length ∧
          offset (rank + 1) + position < table.length
        omega)
    rw [written, Nat.add_sub_cancel_left, ← Slice.getElem!_Nat_eq]
    have coefficients := nextRow_coefficients (row table rank) (row table (rank + 1)) directionValue
      position (by rw [shapeSize]; omega) (by rw [previousSize, shapeSize]; omega)
    simpa only [replacement, previousSize, meaning] using coefficients
  · intro position outside
    rw [exactOutput]
    rcases outside with before | after
    · exact Slice.setSlice!_getElem!_prefix _ _ _ _ before
    · apply Slice.setSlice!_getElem!_suffix
      change offset (rank + 1) + replacement.length ≤ position
      rw [replacementSize]
      have ending := offset_succ (rank + 1)
      omega

end BulksketchBridge.AffineSubspaces
