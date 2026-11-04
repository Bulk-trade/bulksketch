import BulksketchBridge.MapsCanonicalTraceChallenges
import BulksketchBridge.Square
import BulksketchProofs.Field.Maps

/-!
Total correctness of the original canonical-trace fallback and its complete
source loop. The invariant retains both the accumulated conjugate sum and the
last conjugate. All iterator advances terminate by the decreasing remainder.
The independently proved absolute-trace selector discharges the source assert
and checked conversion for every native-width input.
-/

namespace BulksketchBridge.MapsCanonicalTrace

open Aeneas Aeneas.Std Aeneas.Std.WP BulksketchProofs.Field

private def sumWord (input : U64) (count : Nat) : U64 :=
  ⟨Maps.traceSumPrefix count input.bv⟩

private def conjugateWord (input : U64) (count : Nat) : U64 :=
  ⟨Period.iterateSquare (count - 1) input.bv⟩

private theorem normal_of_spec {α : Type} (computation : Result α) (post : α → Prop)
    (h : computation ⦃ post ⦄) : ∃ value, computation = Result.ok value ∧ post value := by
  cases computation using Result.cases with
  | ret value => exact ⟨value, rfl, (spec_ok value).mp h⟩
  | vis effect continuation => exact False.elim ((spec_vis effect continuation).mp h)
  | div => exact False.elim ((spec_div).mp h)

private theorem square_conjugate (input : U64) (count : Nat) (positive : 1 ≤ count) :
    Square.expectedWord (conjugateWord input count) = conjugateWord input (count + 1) := by
  apply U64.bv_eq_imp_eq
  change Period.squareWord (Period.iterateSquare (count - 1) input.bv) =
    Period.iterateSquare ((count + 1) - 1) input.bv
  rw [Nat.add_sub_cancel]
  have previous : count = (count - 1) + 1 := by omega
  conv_rhs => rw [previous]
  rfl

private theorem accumulate_conjugate (input : U64) (count : Nat) (positive : 1 ≤ count) :
    sumWord input count ^^^ Square.expectedWord (conjugateWord input count) =
      sumWord input (count + 1) := by
  rw [square_conjugate input count positive]
  apply U64.bv_eq_imp_eq
  change Maps.traceSumPrefix count input.bv ^^^
    Period.iterateSquare ((count + 1) - 1) input.bv =
      Maps.traceSumPrefix (count + 1) input.bv
  rw [Nat.add_sub_cancel]
  rfl

/-- Every valid suffix of the original 63-step source loop returns the complete
sum, with both loop-carried quantities fixed by the mathematical prefix. -/
theorem loop_refines (input : U64) (range : core.ops.range.Range U32)
    (positive : 1 ≤ range.start.val) (ordered : range.start.val ≤ range.«end».val)
    (endpoint : range.«end».val = 64) :
    bulksketch.field.maps.canonical_trace_loop
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range
      (sumWord input range.start.val) (conjugateWord input range.start.val) =
        Result.ok (sumWord input 64) := by
  suffices ∀ remaining (range : core.ops.range.Range U32),
      1 ≤ range.start.val → range.start.val ≤ range.«end».val →
      range.«end».val = 64 → 64 - range.start.val = remaining →
      bulksketch.field.maps.canonical_trace_loop
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range
        (sumWord input range.start.val) (conjugateWord input range.start.val) =
          Result.ok (sumWord input 64) from
    this (64 - range.start.val) range positive ordered endpoint rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro range positive ordered endpoint remainingEq
    by_cases active : range.start.val < range.«end».val
    · obtain ⟨⟨option, advanced⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_some_spec range active)
      rcases nextPost with ⟨rfl, advanceEq, advanceEnd⟩
      have advancedPositive : 1 ≤ advanced.start.val := by rw [advanceEq]; omega
      have advancedOrdered : advanced.start.val ≤ advanced.«end».val := by
        rw [advanceEq, advanceEnd]
        omega
      have advancedEndpoint : advanced.«end».val = 64 := by rw [advanceEnd, endpoint]
      have decreased : 64 - advanced.start.val < remaining := by
        rw [advanceEq]
        omega
      have recursive := inductionHypothesis (64 - advanced.start.val) decreased advanced
        advancedPositive advancedOrdered advancedEndpoint rfl
      have bodyNormal : bulksketch.field.maps.canonical_trace_loop.body
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range
          (sumWord input range.start.val) (conjugateWord input range.start.val) =
            Result.ok (ControlFlow.cont (advanced,
              sumWord input advanced.start.val, conjugateWord input advanced.start.val)) := by
        simp only [bulksketch.field.maps.canonical_trace_loop.body, nextNormal, bind_ok,
          Square.square_refines]
        simp only [lift, bind_ok]
        simp only [advanceEq, ← square_conjugate input range.start.val positive,
          ← accumulate_conjugate input range.start.val positive]
        rfl
      unfold bulksketch.field.maps.canonical_trace_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok]
      change bulksketch.field.maps.canonical_trace_loop
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField advanced
        (sumWord input advanced.start.val) (conjugateWord input advanced.start.val) = _
      exact recursive
    · have stopped : range.start.val ≥ range.«end».val := by omega
      obtain ⟨⟨option, unchanged⟩, nextNormal, nextPost⟩ := normal_of_spec _ _
        (core.iter.range.IteratorRange.next_U32_none_spec range stopped)
      rcases nextPost with ⟨optionEq, unchangedEq⟩
      rw [optionEq, unchangedEq] at nextNormal
      have atEnd : range.start.val = 64 := by omega
      have bodyNormal : bulksketch.field.maps.canonical_trace_loop.body
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField range
          (sumWord input range.start.val) (conjugateWord input range.start.val) =
            Result.ok (ControlFlow.done (sumWord input range.start.val)) := by
        simp only [bulksketch.field.maps.canonical_trace_loop.body, nextNormal, bind_ok]
        rfl
      unfold bulksketch.field.maps.canonical_trace_loop
      unfold loop
      dsimp only
      rw [bodyNormal]
      simp only [bind_ok, atEnd]

private theorem initial_sum (input : U64) : sumWord input 1 = input := by
  apply U64.bv_eq_imp_eq
  simp only [sumWord, Maps.traceSumPrefix, Period.iterateSquare]
  change (0 : BitVec 64) ^^^ input.bv = input.bv
  exact BitVec.zero_xor

private theorem initial_conjugate (input : U64) : conjugateWord input 1 = input := rfl

private theorem complete_sum_bounded (input : U64) : (sumWord input 64).val ≤ 1 := by
  change (Maps.traceSumPrefix 64 input.bv).toNat ≤ 1
  rw [← Maps.absoluteTrace_is_sum input.bv, Maps.absoluteTrace_eq_selector input.bv]
  cases bitCase : Maps.traceBit input.bv <;> simp [Maps.traceWord, bitCase]

private theorem conversion_normal (input : U64) :
    U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from (sumWord input 64) =
      Result.ok (.Ok (expectedWord input)) := by
  have inRange : (sumWord input 64).val ≤ UScalar.max .U8 :=
    (complete_sum_bounded input).trans (by simp [U8.max_eq])
  simp only [U8.Insts.CoreConvertTryFromU64TryFromIntError.try_from,
    core.num.tryFromUScalar, inRange, ite_true]
  congr 2
  apply U8.bv_eq_imp_eq
  change (Maps.traceSumPrefix 64 input.bv).setWidth 8 =
    (Maps.absoluteTrace input.bv).setWidth 8
  rw [Maps.absoluteTrace_is_sum input.bv]

/-- The full fallback computation returns its mathematical trace byte for every
U64 input; its assertion and checked conversion are proved successful. -/
theorem canonical_trace_refines :
    MapsCanonicalTraceChallenges.normalResultMatchesAbsoluteTrace := by
  intro input
  have initialLoop := loop_refines input { start := 1#u32, «end» := 64#u32 }
    (by simp) (by simp) (by simp)
  simp only [show (1#u32).val = 1 from rfl, initial_sum, initial_conjugate] at initialLoop
  have boundedSource : sumWord input 64 ≤ 1#u64 := by
    simpa using complete_sum_bounded input
  have assertNormal : massert (sumWord input 64 ≤ 1#u64) = Result.ok () :=
    (massert_ok _).mpr boundedSource
  simp only [bulksketch.field.maps.canonical_trace,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    bind_ok, initialLoop, assertNormal, conversion_normal, core.result.Result.expect]

end BulksketchBridge.MapsCanonicalTrace
