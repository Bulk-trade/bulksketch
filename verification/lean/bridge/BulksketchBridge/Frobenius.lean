import BulksketchBridge.FrobeniusChallenges
import BulksketchBridge.Square

/-!
Total correctness of the original extracted portable repeated-square loop.
The real Gf64 dictionary makes canonicality unconditional and the divisor 64.
Every source iterator step is justified; the decreasing natural remainder proves
termination. No field-period or irreducibility statement is used.
-/

namespace BulksketchBridge.Frobenius

open Aeneas Aeneas.Std Aeneas.Std.WP

private theorem normal_of_spec {α : Type} (computation : Result α) (post : α → Prop)
    (h : computation ⦃ post ⦄) : ∃ value, computation = Result.ok value ∧ post value := by
  cases computation using Result.cases with
  | ret value => exact ⟨value, rfl, (spec_ok value).mp h⟩
  | vis effect continuation => exact False.elim ((spec_vis effect continuation).mp h)
  | div => exact False.elim ((spec_div).mp h)

private theorem repeatedSquare_after_square (count : Nat) (input : BitVec 64) :
    repeatedSquare count (squareBits input) = repeatedSquare (count + 1) input := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [repeatedSquare, ih]

/-- Every bounded suffix of the original source loop returns normally with the
complete remaining sequence of polynomial-square remainders. -/
theorem loop_refines (range : core.ops.range.Range U32) (input : U64)
    (ordered : range.start.val ≤ range.«end».val) (bounded : range.«end».val ≤ 63) :
    bulksketch.field.gf64.frobenius_loop
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range input =
        Result.ok (⟨repeatedSquare (range.«end».val - range.start.val) input.bv⟩ : U64) := by
  suffices ∀ remaining (range : core.ops.range.Range U32) (input : U64),
      range.start.val ≤ range.«end».val → range.«end».val ≤ 63 →
      range.«end».val - range.start.val = remaining →
      bulksketch.field.gf64.frobenius_loop
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range input =
          Result.ok (⟨repeatedSquare (range.«end».val - range.start.val) input.bv⟩ : U64) from
    this (range.«end».val - range.start.val) range input ordered bounded rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro range input ordered bounded remainingEq
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨⟨option, advanced⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_some_spec range active)
      rcases nextPost with ⟨rfl, advanceEq, advanceEnd⟩
      have advancedOrdered : advanced.start.val ≤ advanced.«end».val := by
        rw [advanceEq, advanceEnd]
        omega
      have advancedBounded : advanced.«end».val ≤ 63 := by
        rw [advanceEnd]
        exact bounded
      have decreased : advanced.«end».val - advanced.start.val < remaining := by
        rw [advanceEq, advanceEnd]
        omega
      have recursive := ih (advanced.«end».val - advanced.start.val) decreased advanced
        (Square.expectedWord input) advancedOrdered advancedBounded rfl
      have bodyNormal : bulksketch.field.gf64.frobenius_loop.body
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range input =
            Result.ok (ControlFlow.cont (advanced, Square.expectedWord input)) := by
        simp only [bulksketch.field.gf64.frobenius_loop.body, nextNormal, bind_ok,
          Square.square_refines]
        rfl
      unfold bulksketch.field.gf64.frobenius_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok]
      change bulksketch.field.gf64.frobenius_loop
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField advanced
        (Square.expectedWord input) = _
      rw [recursive]
      congr 1
      apply U64.bv_eq_imp_eq
      change repeatedSquare (advanced.«end».val - advanced.start.val)
        (squareBits input.bv) = repeatedSquare (range.«end».val - range.start.val) input.bv
      rw [repeatedSquare_after_square]
      congr 1
      rw [advanceEq, advanceEnd]
      omega
    · have stopped : range.start.val ≥ range.«end».val := by omega
      obtain ⟨⟨option, unchanged⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_none_spec range stopped)
      rcases nextPost with ⟨optionEq, unchangedEq⟩
      rw [optionEq, unchangedEq] at nextNormal
      have noRemaining : range.«end».val - range.start.val = 0 := by omega
      have bodyNormal : bulksketch.field.gf64.frobenius_loop.body
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range input =
            Result.ok (ControlFlow.done input) := by
        simp only [bulksketch.field.gf64.frobenius_loop.body, nextNormal, bind_ok]
        rfl
      unfold bulksketch.field.gf64.frobenius_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok, noRemaining, repeatedSquare]

private theorem canonical_mask (word : U64) :
    word &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
  apply U64.bv_eq_imp_eq
  simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK,
    core.num.U64.MAX, U64.rMax]

/-- Every original Gf64 call, for every word and every U32 power, returns exactly
the frozen independent model after power modulo 64 squarings. -/
theorem frobenius_refines :
    BulksketchBridge.FrobeniusChallenges.normalResultMatchesIteratedSquare := by
  intro input power
  obtain ⟨remainder, remainderNormal, remainderEq⟩ := normal_of_spec _ _
    (U32.rem_spec power (y := 64#u32) (by decide))
  change remainder.val = power.val % 64 at remainderEq
  have remainderBound : remainder.val ≤ 63 := by
    rw [remainderEq]
    have bound := Nat.mod_lt power.val (by decide : 0 < 64)
    omega
  simp only [bulksketch.field.gf64.frobenius,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    lift, bind_ok, canonical_mask, ite_true, remainderNormal]
  have complete := loop_refines { start := 0#u32, «end» := remainder } input
    (by simp) remainderBound
  have zeroValue : (0#u32).val = 0 := by rfl
  simpa only [zeroValue, Nat.sub_zero, remainderEq, expectedWord,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS] using complete

end BulksketchBridge.Frobenius
