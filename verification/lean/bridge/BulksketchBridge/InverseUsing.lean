import BulksketchBridge.InverseUsingChallenges
import BulksketchBridge.InverseNative

/-! The original captured callback is now represented by its generated body,
including its range iterator. The explicitly recorded reviewed frontend variant
is a translation trust boundary; no closure correctness model is substituted. -/
namespace BulksketchBridge.InverseUsing

open Aeneas Aeneas.Std Aeneas.Std.WP
open BulksketchProofs.Field

private theorem normal_of_spec {α : Type} (computation : Result α) (post : α → Prop)
    (proof : computation ⦃ post ⦄) :
    ∃ value, computation = Result.ok value ∧ post value := by
  cases computation using Result.cases with
  | ret value => exact ⟨value, rfl, (spec_ok value).mp proof⟩
  | vis effect continuation => exact False.elim ((spec_vis effect continuation).mp proof)
  | div => exact False.elim ((spec_div).mp proof)

private theorem iterate_after_square (count : Nat) (input : BitVec 64) :
    Period.iterateSquare count (Period.squareWord input) =
      Period.iterateSquare (count + 1) input := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
    simp only [Period.iterateSquare, inductionHypothesis]

/-- The remaining range length decreases for every original iterator step.
All U32 end points, including the maximum, are admitted. -/
theorem captured_loop_refines {F T1 T2 : Type}
    (square : core.ops.function.Fn T2 U64 U64)
    (callback : bulksketch.field.maps.inverse_using.closure F T1 T2)
    (nativeSquare : ∀ input, square.call callback input =
      bulksketch.field.gf64.square
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input)
    (range : core.ops.range.Range U32) (input : U64)
    (ordered : range.start.val ≤ range.«end».val) :
    bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
      square callback range input =
        Result.ok (⟨Period.iterateSquare (range.«end».val - range.start.val) input.bv⟩ : U64) := by
  suffices ∀ remaining (range : core.ops.range.Range U32) (input : U64),
      range.start.val ≤ range.«end».val →
      range.«end».val - range.start.val = remaining →
      bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
        square callback range input =
          Result.ok (⟨Period.iterateSquare (range.«end».val - range.start.val) input.bv⟩ : U64) from
    this (range.«end».val - range.start.val) range input ordered rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro range input ordered remainingEq
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨⟨option, advanced⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_some_spec range active)
      rcases nextPost with ⟨rfl, advanceEq, advanceEnd⟩
      have advancedOrdered : advanced.start.val ≤ advanced.«end».val := by
        rw [advanceEq, advanceEnd]
        omega
      have decreased : advanced.«end».val - advanced.start.val < remaining := by
        rw [advanceEq, advanceEnd]
        omega
      have recursive := inductionHypothesis (advanced.«end».val - advanced.start.val)
        decreased advanced (Square.expectedWord input) advancedOrdered rfl
      have bodyNormal :
          bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop.body
            square callback range input =
              Result.ok (ControlFlow.cont (advanced, Square.expectedWord input)) := by
        simp only [bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop.body,
          nextNormal, bind_ok, nativeSquare, Square.square_refines]
        rfl
      unfold bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok]
      change bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
        (F := F) (T1 := T1) square callback advanced (Square.expectedWord input) = _
      rw [recursive]
      congr 1
      apply U64.bv_eq_imp_eq
      change Period.iterateSquare (advanced.«end».val - advanced.start.val)
        (Period.squareWord input.bv) =
          Period.iterateSquare (range.«end».val - range.start.val) input.bv
      rw [iterate_after_square]
      congr 1
      rw [advanceEq, advanceEnd]
      omega
    · have stopped : range.start.val ≥ range.«end».val := by omega
      obtain ⟨⟨option, unchanged⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_none_spec range stopped)
      rcases nextPost with ⟨optionEq, unchangedEq⟩
      rw [optionEq, unchangedEq] at nextNormal
      have noRemaining : range.«end».val - range.start.val = 0 := by omega
      have bodyNormal :
          bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop.body
            (F := F) (T1 := T1) square callback range input =
              Result.ok (ControlFlow.done input) := by
        simp only [bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop.body,
          nextNormal, bind_ok]
        rfl
      unfold bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok, noRemaining, Period.iterateSquare]

/-- Complete unmodded iteration semantics for the actual generated closure. -/
theorem captured_square_refines : InverseUsingChallenges.capturedSquareReturnsEveryIteration := by
  intro T1 T2 multiply square callback nativeSquare input power
  exact captured_loop_refines (F := bulksketch.field.Gf64) (T1 := T1)
    square callback nativeSquare { start := 0#u32, «end» := power } input (by simp)

/-- The original enclosing wrapper computes the unique represented inverse. -/
theorem inverse_using_refines : InverseUsingChallenges.actualInverseUsingReturnsFieldInverse := by
  intro T1 T2 multiply square mulCallback squareCallback nativeMul nativeSquare input
  unfold bulksketch.field.maps.inverse_using
  apply Inverse.field_inverse_refines
  · exact nativeMul
  · intro value count
    change bulksketch.field.maps.inverse_using.closure.Insts.CoreOpsFunctionFnPairU64U32U64.call
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField multiply square squareCallback
      (value, count) = _
    rw [captured_square_refines T1 T2 multiply square squareCallback nativeSquare,
      FrobeniusPeriod.native_unmodded_refines]

/-- No callback behavior is assumed for the public scalar inversion wrapper. -/
theorem inverse_refines : InverseUsingChallenges.actualInverseReturnsFieldInverse := by
  intro input
  unfold bulksketch.field.maps.inverse
  apply inverse_using_refines
  · intro left right
    rfl
  · intro value
    rfl

end BulksketchBridge.InverseUsing
