import BulksketchBridge.FrobeniusConst
import BulksketchBridge.FrobeniusTableSpec
import BulksketchBridge.FrobeniusTablesSupport

/-! The original inverse table generator visits basis positions in order. At
an inner-loop prefix, exactly the completed values in the current row have
received that position's Frobenius column. Each entry is the image of its
partial placed nibble, by linearity of the checked square iteration. -/

namespace BulksketchBridge.FrobeniusInverseTable

open Aeneas Aeneas.Std BulksketchProofs.Field
open FrobeniusTable FrobeniusTables

/-- A nibble contributes only to its four assigned basis coefficients. -/
private theorem placed_word_bit (row value bit : Nat) (valueBound : value < 16) (bitBound : bit < 64) :
    ((BitVec.ofNat 64 value) <<< (4 * row)).getLsbD bit =
      if row = bit / 4 then value.testBit (bit % 4) else false := by
  rw [BitVec.getLsbD_shiftLeft]
  by_cases same : row = bit / 4
  · subst row
    have before : ¬bit < 4 * (bit / 4) := by omega
    have offset : bit - 4 * (bit / 4) = bit % 4 := by omega
    simp only [before, bitBound, offset, BitVec.getLsbD_ofNat, show bit % 4 < 64 by omega,
      decide_true, decide_false, Bool.not_false, Bool.true_and, ite_true]
  · by_cases before : bit < 4 * row
    · simp [same, before]
    · have above : 4 ≤ bit - 4 * row := by omega
      have clear : value.testBit (bit - 4 * row) = false :=
        Nat.testBit_lt_two_pow (valueBound.trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) above))
      simp only [same, ite_false, BitVec.getLsbD_ofNat, clear, Bool.and_false]

/-- The original signed counter loop applies exactly the remaining squares. -/
private theorem power_loop (input : U64) (count : Nat) (bound : count ≤ 21) :
    bulksketch.field.frobenius.inverse21_table_loop0_loop0
      (⟨Period.iterateSquare count input.bv⟩ : U64) (FrobeniusConst.counter count) =
        Result.ok (⟨Period.iterateSquare 21 input.bv⟩ : U64) := by
  suffices ∀ remaining count, count ≤ 21 → 21 - count = remaining →
      bulksketch.field.frobenius.inverse21_table_loop0_loop0
        (⟨Period.iterateSquare count input.bv⟩ : U64) (FrobeniusConst.counter count) =
          Result.ok (⟨Period.iterateSquare 21 input.bv⟩ : U64) from
    this (21 - count) count bound rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count bound remainingEq
    unfold bulksketch.field.frobenius.inverse21_table_loop0_loop0
    unfold loop
    dsimp only
    by_cases active : count < 21
    · have guard : FrobeniusConst.counter count < 21#i32 := by
        rw [IScalar.lt_equiv, FrobeniusConst.counter_value count (by omega)]
        change (count : Int) < 21
        omega
      simp only [bulksketch.field.frobenius.inverse21_table_loop0_loop0.body, guard, ite_true,
        FrobeniusConst.square_refines (⟨Period.iterateSquare count input.bv⟩ : U64), bind_ok,
        FrobeniusConst.counter_add count (by omega)]
      exact ih (21 - (count + 1)) (by omega) (count + 1) (by omega) rfl
    · have done : count = 21 := by omega
      subst count
      have terminal : bulksketch.field.frobenius.inverse21_table_loop0_loop0.body
          (⟨Period.iterateSquare 21 input.bv⟩ : U64) (FrobeniusConst.counter 21) =
          Result.ok (ControlFlow.done (⟨Period.iterateSquare 21 input.bv⟩ : U64)) := by rfl
      rw [terminal]
      simp only [bind_ok]

private def expectedPrefix (bit done row value : Nat) : BitVec 64 :=
  Period.iterateSquare 21 (Period.xorPrefix (BitVec.ofNat 64 value <<< (4 * row))
    (if row = bit / 4 ∧ value < done then bit + 1 else bit))

private def Prefix (table : Map) (bit done : Nat) : Prop :=
  ∀ row value, row < 16 → value < 16 →
    (entry (entry table row) value).bv = expectedPrefix bit done row value

private theorem prefix_value_step (bit done row value : Nat) (bitBound : bit < 64)
    (valueBound : value < 16) :
    expectedPrefix bit (done + 1) row value = expectedPrefix bit done row value ^^^
      (if row = bit / 4 ∧ value = done ∧ value.testBit (bit % 4) = true then
        Period.iterateSquare 21 ((1 : BitVec 64) <<< bit) else 0) := by
  by_cases changed : row = bit / 4 ∧ value = done
  · obtain ⟨rfl, rfl⟩ := changed
    simp only [expectedPrefix, true_and, lt_add_one, lt_self_iff_false, ite_true,
      ite_false, Period.xorPrefix, placed_word_bit _ _ _ valueBound bitBound]
    cases value.testBit (bit % 4) with
    | false => simp
    | true => simp [Period.iterateSquare_xor]
  · have samePrefix : (row = bit / 4 ∧ value < done + 1) ↔ row = bit / 4 ∧ value < done := by
      omega
    have noUpdate : ¬(row = bit / 4 ∧ value = done ∧ value.testBit (bit % 4) = true) := by
      intro h
      exact changed ⟨h.1, h.2.1⟩
    simp only [expectedPrefix, samePrefix, noUpdate, ite_false]
    simp

private theorem finish_bit (table : Map) (bit : Nat) (bitBound : bit < 64)
    (complete : Prefix table bit 16) : Prefix table (bit + 1) 0 := by
  intro row value rowBound valueBound
  rw [complete row value rowBound valueBound]
  unfold expectedPrefix
  simp only [Nat.not_lt_zero, and_false, ite_false]
  by_cases same : row = bit / 4
  · simp [same, valueBound]
  · simp only [same, false_and, ite_false, Period.xorPrefix,
      placed_word_bit row value bit valueBound bitBound, Bool.false_eq_true]
    simp

private theorem initial_prefix :
    Prefix (Array.repeat 16#usize (Array.repeat 16#usize 0#u64)) 0 0 := by
  intro row value rowBound valueBound
  simp only [entry_repeat (16#usize) (Array.repeat 16#usize 0#u64) row (by simpa using rowBound),
    entry_repeat (16#usize) (0#u64) value (by simpa using valueBound), expectedPrefix,
    Nat.not_lt_zero, and_false, ite_false, Period.xorPrefix, Period.iterateSquare_zero]
  rfl

private theorem mask_selects_bit (value offset : Usize) (bound : offset.val < 4) :
    ∃ mask : Usize, (1#usize) <<< offset = Result.ok mask ∧
      ((value &&& mask ≠ 0#usize) ↔ value.val.testBit offset.val = true) := by
  have shiftBound : offset.val < System.Platform.numBits := by
    rcases System.Platform.numBits_eq with width | width <;> omega
  obtain ⟨mask, normal, _, bits⟩ := RawMulTable.normal_of_spec _ _
    (Usize.ShiftLeft_spec (1#usize) offset shiftBound)
  refine ⟨mask, normal, ?_⟩
  rw [ne_eq, UScalar.eq_equiv_bv_eq]
  simp only [UScalar.bv_and, bits, Usize.ofNat_bv]
  change (value.bv &&& ((1 : BitVec System.Platform.numBits) <<< offset.val) ≠ 0) ↔ _
  simpa only [BitVec.getLsbD, UScalar.bv_toNat] using
    FrobeniusConst.masked_single_bit value.bv offset.val shiftBound

/-- A normal step proves both bounds and the exact set of updated cells. -/
private theorem value_body (table : Map) (bit value : Usize)
    (bitBound : bit.val < 64) (valueBound : value.val < 16)
    (invariant : Prefix table bit.val value.val) :
    ∃ nextTable : Map, ∃ next : Usize,
      bulksketch.field.frobenius.inverse21_table_loop0_loop1.body bit
        (⟨Period.iterateSquare 21 ((1 : BitVec 64) <<< bit.val)⟩ : U64) table value =
          Result.ok (ControlFlow.cont (nextTable, next)) ∧
      next.val = value.val + 1 ∧ Prefix nextTable bit.val next.val := by
  obtain ⟨offset, modNormal, modValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.rem_spec bit (y := 4#usize) (by simp))
  change offset.val = bit.val % (4#usize).val at modValue
  rw [show (4#usize).val = 4 by simp] at modValue
  obtain ⟨mask, shiftNormal, selects⟩ := mask_selects_bit value offset (by omega)
  rw [modValue] at selects
  obtain ⟨next, nextNormal, nextValue⟩ := usize_succ value (by omega)
  have active : value < 16#usize := by
    rw [UScalar.lt_equiv, show (16#usize).val = 16 by simp]
    exact valueBound
  by_cases selected : value.val.testBit (bit.val % 4) = true
  · obtain ⟨row, divNormal, divValue⟩ := RawMulTable.normal_of_spec _ _
      (Usize.div_spec bit (y := 4#usize) (by simp))
    change row.val = bit.val / (4#usize).val at divValue
    rw [show (4#usize).val = 4 by simp] at divValue
    have rowBound : row.val < (16#usize).val := by simp; omega
    have slotBound : value.val < (16#usize).val := by simpa using valueBound
    let column : U64 := ⟨Period.iterateSquare 21 ((1 : BitVec 64) <<< bit.val)⟩
    let previous := entry table row.val
    let updated := entry previous value.val ^^^ column
    refine ⟨table.set row (previous.set value updated), next, ?_, nextValue, ?_⟩
    · simp only [bulksketch.field.frobenius.inverse21_table_loop0_loop1.body, active,
        ite_true, modNormal, shiftNormal, lift, bind_ok, bne_iff_ne, selects, selected,
        divNormal, read_normal table row rowBound, read_normal (entry table row.val) value slotBound,
        read_mut_normal table row rowBound, nextNormal]
      change (do
        let table1 ← (do
          let row1 ← Array.update previous value updated
          Result.ok (Aeneas.Std.Array.set table row row1))
        Result.ok (ControlFlow.cont (table1, next))) = _
      simp only [update_normal previous value updated slotBound, Bind.bind, bind_ok]
    · intro r v hr hv
      rw [nextValue, prefix_value_step _ _ _ _ bitBound hv, ← invariant r v hr hv]
      by_cases sameRow : r = row.val
      · subst r
        rw [entry_set_same _ _ _ rowBound]
        by_cases sameValue : v = value.val
        · subst v
          rw [entry_set_same _ _ _ slotBound]
          simp [updated, column, previous, divValue, selected]
        · rw [entry_set_other _ _ _ _ (Ne.symm sameValue)]
          simp [previous, sameValue]
      · rw [entry_set_other _ _ _ _ (Ne.symm sameRow)]
        simp [sameRow, ← divValue]
  · refine ⟨table, next, ?_, nextValue, ?_⟩
    · simp only [bulksketch.field.frobenius.inverse21_table_loop0_loop1.body, active,
        ite_true, modNormal, shiftNormal, lift, bind_ok, bne_iff_ne, selects, selected,
        Bool.false_eq_true, ite_false, nextNormal]
    · intro row slot rowBound slotBound
      rw [nextValue, prefix_value_step _ _ _ _ bitBound slotBound, invariant row slot rowBound slotBound]
      by_cases same : slot = value.val
      · simp [same, selected]
      · simp [same]

/-- Every suffix of the value loop completes with all sixteen entries updated
for this bit. The rank is the number of unvisited nibble values. -/
private theorem value_loop (table : Map) (bit value : Usize) (bitBound : bit.val < 64)
    (valueBound : value.val ≤ 16) (invariant : Prefix table bit.val value.val) :
    ∃ completed : Map,
      bulksketch.field.frobenius.inverse21_table_loop0_loop1 table bit
        (⟨Period.iterateSquare 21 ((1 : BitVec 64) <<< bit.val)⟩ : U64) value =
          Result.ok completed ∧ Prefix completed bit.val 16 := by
  suffices ∀ remaining (table : Map) (value : Usize), value.val ≤ 16 →
      16 - value.val = remaining → Prefix table bit.val value.val →
      ∃ completed : Map,
        bulksketch.field.frobenius.inverse21_table_loop0_loop1 table bit
          (⟨Period.iterateSquare 21 ((1 : BitVec 64) <<< bit.val)⟩ : U64) value =
            Result.ok completed ∧ Prefix completed bit.val 16 from
    this (16 - value.val) table value valueBound rfl invariant
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro table value valueBound remainingEq invariant
    by_cases active : value.val < 16
    · obtain ⟨nextTable, next, step, nextValue, nextInvariant⟩ :=
        value_body table bit value bitBound active invariant
      obtain ⟨completed, normal, complete⟩ :=
        ih (16 - next.val) (by omega) nextTable next (by omega) rfl nextInvariant
      refine ⟨completed, ?_, complete⟩
      unfold bulksketch.field.frobenius.inverse21_table_loop0_loop1
      unfold loop
      dsimp only
      rw [step]
      simp only [bind_ok]
      exact normal
    · have atEnd : value.val = 16 := by omega
      have guard : ¬ value < 16#usize := by
        rw [UScalar.lt_equiv, show (16#usize).val = 16 by simp]
        exact active
      refine ⟨table, ?_, by simpa only [atEnd] using invariant⟩
      unfold bulksketch.field.frobenius.inverse21_table_loop0_loop1
      unfold loop
      dsimp only
      simp only [bulksketch.field.frobenius.inverse21_table_loop0_loop1.body, guard, ite_false, bind_ok]

/-- The outer loop contributes each of the 64 basis positions once. -/
private theorem bit_loop (table : Map) (bit : Usize) (bounded : bit.val ≤ 64)
    (invariant : Prefix table bit.val 0) :
    ∃ completed : Map, bulksketch.field.frobenius.inverse21_table_loop0 table bit =
      Result.ok completed ∧ Prefix completed 64 0 := by
  suffices ∀ remaining (table : Map) (bit : Usize), bit.val ≤ 64 →
      64 - bit.val = remaining → Prefix table bit.val 0 →
      ∃ completed : Map, bulksketch.field.frobenius.inverse21_table_loop0 table bit =
        Result.ok completed ∧ Prefix completed 64 0 from
    this (64 - bit.val) table bit bounded rfl invariant
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro table bit bounded remainingEq invariant
    by_cases active : bit.val < 64
    · have guard : bit < 64#usize := by
        rw [UScalar.lt_equiv, show (64#usize).val = 64 by simp]
        exact active
      obtain ⟨column, shiftNormal, _, bits⟩ := RawMulTable.normal_of_spec _ _
        (U64.ShiftLeft_spec (1#u64) bit active)
      have columnEq : column = (⟨(1 : BitVec 64) <<< bit.val⟩ : U64) :=
        U64.bv_eq_imp_eq _ _ bits
      subst column
      have squareNormal := power_loop (⟨(1 : BitVec 64) <<< bit.val⟩ : U64) 0 (by decide)
      change bulksketch.field.frobenius.inverse21_table_loop0_loop0
        (⟨(1 : BitVec 64) <<< bit.val⟩ : U64) (0#i32) = _ at squareNormal
      obtain ⟨nextTable, valuesNormal, valuesComplete⟩ :=
        value_loop table bit (0#usize) active (by simp) (by simpa using invariant)
      obtain ⟨nextBit, nextNormal, nextValue⟩ := usize_succ bit (by omega)
      have nextInvariant : Prefix nextTable nextBit.val 0 := by
        rw [nextValue]
        exact finish_bit nextTable bit.val active valuesComplete
      obtain ⟨completed, normal, complete⟩ :=
        ih (64 - nextBit.val) (by omega) nextTable nextBit (by omega) rfl nextInvariant
      refine ⟨completed, ?_, complete⟩
      have step : bulksketch.field.frobenius.inverse21_table_loop0.body table bit =
          Result.ok (ControlFlow.cont (nextTable, nextBit)) := by
        simp only [bulksketch.field.frobenius.inverse21_table_loop0.body, guard, ite_true,
          shiftNormal, squareNormal, valuesNormal, nextNormal, bind_ok]
      unfold bulksketch.field.frobenius.inverse21_table_loop0
      unfold loop
      dsimp only
      rw [step]
      simp only [bind_ok]
      exact normal
    · have atEnd : bit.val = 64 := by omega
      have guard : ¬ bit < 64#usize := by
        rw [UScalar.lt_equiv, show (64#usize).val = 64 by simp]
        exact active
      refine ⟨table, ?_, by simpa only [atEnd] using invariant⟩
      unfold bulksketch.field.frobenius.inverse21_table_loop0
      unfold loop
      dsimp only
      simp only [bulksketch.field.frobenius.inverse21_table_loop0.body, guard, ite_false, bind_ok]

/-- The original const generator returns normally, and every one of its 256
cells is exactly the 21st Frobenius image of the corresponding placed nibble. -/
theorem inverse21_table_refines : InverseTableRefines := by
  obtain ⟨table, normal, complete⟩ :=
    bit_loop (Array.repeat 16#usize (Array.repeat 16#usize 0#u64)) (0#usize) (by simp)
      (by simpa using initial_prefix)
  refine ⟨table, ?_, ?_⟩
  · simp only [bulksketch.field.frobenius.inverse21_table, normal]
  · intro row value rowBound valueBound
    simpa only [cellAt, Array.getElem!_Nat_eq, entry, expectedPrefix, Nat.not_lt_zero,
      and_false, ite_false, Period.xorPrefix_complete, cell] using
        complete row value rowBound valueBound

end BulksketchBridge.FrobeniusInverseTable
