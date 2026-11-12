import BulksketchBridge.InverseSpec
import Mathlib.Tactic.IntervalCases

namespace BulksketchBridge.Inverse

open Aeneas Aeneas.Std

set_option maxRecDepth 4096

private theorem iterator_step (remaining : Nat) (bounded : remaining < 5) :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32)
      (iteratorAt (remaining + 1)) =
        Result.ok (some (⟨BitVec.ofNat 32 remaining⟩ : U32), iteratorAt remaining) := by
  interval_cases remaining <;> simp [iteratorAt,
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.UScalarStep.backward_checked,
    core.iter.range.StepU32, core.iter.range.UScalarStep, core.cmp.PartialOrdU32,
    core.cmp.impls.PartialOrdU32.lt, liftFun2, UScalar.val, UScalar.ofNatCore]

private theorem iterator_done :
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32)
      (iteratorAt 0) = Result.ok (none, iteratorAt 0) := by
  simp [iteratorAt,
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
    core.ops.range.Range.Insts.CoreIterTraitsDoubleEndedIterator.next_back,
    core.iter.range.StepU32, core.iter.range.UScalarStep, core.cmp.PartialOrdU32,
    core.cmp.impls.PartialOrdU32.lt, liftFun2, UScalar.val, UScalar.ofNatCore]

theorem body_step {T1 T2 : Type}
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2)
    (multiply : U64 → U64 → U64) (frobenius : U64 → U32 → U64)
    (mulNormal : MulNormal mulDict mulCallback multiply)
    (frobNormal : FrobeniusNormal frobDict frobCallback frobenius)
    (input value : U64) (count : Nat) (bounded : count < 5) :
    bulksketch.field.maps.inverse_with_frobenius_loop.body mulDict frobDict input
      mulCallback frobCallback (63#u32) (iteratorAt (5 - count)) (chainIndex count) value =
      Result.ok (ControlFlow.cont (iteratorAt (5 - (count + 1)), chainIndex (count + 1),
        multiply (frobenius (multiply (frobenius value (chainIndex count)) value) (1#u32)) input)) := by
  unfold MulNormal at mulNormal
  unfold FrobeniusNormal at frobNormal
  have nextNormal := iterator_step (4 - count) (by omega)
  have remainingEq : 5 - count = (4 - count) + 1 := by omega
  rw [← remainingEq] at nextNormal
  simp only [bulksketch.field.maps.inverse_with_frobenius_loop.body, nextNormal,
    bind_ok, mulNormal, frobNormal]
  dsimp! only
  have doubled : chainIndex count * 2#u32 =
      Result.ok (⟨BitVec.ofNat 32 (2 * (2 ^ (count + 1) - 1))⟩ : U32) := by
    interval_cases count <;> rfl
  have appended : (⟨BitVec.ofNat 32 (2 * (2 ^ (count + 1) - 1))⟩ : U32) + 1#u32 =
      Result.ok (chainIndex (count + 1)) := by
    interval_cases count <;> rfl
  have shifted : (1#u32) <<< (⟨BitVec.ofNat 32 (4 - count)⟩ : U32) =
      Result.ok (⟨(1 : BitVec 32) <<< (4 - count)⟩ : U32) := by
    interval_cases count <;> rfl
  have selected : ((63#u32) &&& (⟨(1 : BitVec 32) <<< (4 - count)⟩ : U32)) ≠ 0#u32 := by
    interval_cases count <;> decide +kernel
  simp only [doubled, shifted, bind_ok, lift, bne_iff_ne, appended]
  rw [show 5 - (count + 1) = 4 - count by omega]
  exact ite_eq_left selected

/-- Every reachable prefix completes. The remaining reverse-range length is
strictly decreased on each original loop step; all five steps append a one. -/
theorem loop_refines {T1 T2 : Type}
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2)
    (multiply : U64 → U64 → U64) (frobenius : U64 → U32 → U64)
    (mulNormal : MulNormal mulDict mulCallback multiply)
    (frobNormal : FrobeniusNormal frobDict frobCallback frobenius)
    (input : U64) (count : Nat) (bounded : count ≤ 5) :
    bulksketch.field.maps.inverse_with_frobenius_loop mulDict frobDict
      (iteratorAt (5 - count)) input mulCallback frobCallback (63#u32) (chainIndex count)
      (chain multiply frobenius input count) = Result.ok (chain multiply frobenius input 5) := by
  suffices ∀ remaining count, count ≤ 5 → 5 - count = remaining →
      bulksketch.field.maps.inverse_with_frobenius_loop mulDict frobDict
        (iteratorAt (5 - count)) input mulCallback frobCallback (63#u32) (chainIndex count)
        (chain multiply frobenius input count) = Result.ok (chain multiply frobenius input 5) from
    this (5 - count) count bounded rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro count bounded remainingEq
    by_cases active : count < 5
    · have step := body_step mulDict frobDict mulCallback frobCallback multiply frobenius
        mulNormal frobNormal input (chain multiply frobenius input count) count active
      change _ = Result.ok (ControlFlow.cont (iteratorAt (5 - (count + 1)),
        chainIndex (count + 1), chain multiply frobenius input (count + 1))) at step
      have decreased : 5 - (count + 1) < remaining := by omega
      unfold bulksketch.field.maps.inverse_with_frobenius_loop
      unfold loop
      dsimp only
      rw [step]
      simp only [bind_ok]
      exact inductionHypothesis (5 - (count + 1)) decreased (count + 1) (by omega) rfl
    · have atEnd : count = 5 := by omega
      subst count
      unfold bulksketch.field.maps.inverse_with_frobenius_loop
      unfold loop
      dsimp only
      simp only [Nat.sub_self, bulksketch.field.maps.inverse_with_frobenius_loop.body,
        iterator_done, bind_ok]
      dsimp! only
      simp only [bind_ok]

private theorem canonical_mask (input : U64) :
    input &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
  apply U64.bv_eq_imp_eq
  simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK,
    core.num.U64.MAX, U64.rMax]

private theorem target_subtraction : (64#u32) - (1#u32) = Result.ok (63#u32) := by rfl
private theorem target_leading_zeros : core.num.U32.leading_zeros (63#u32) = 26#u32 := by
  apply U32.bv_eq_imp_eq
  decide +kernel
private theorem length_subtraction : core.num.U32.BITS - (26#u32) = Result.ok (6#u32) := by rfl
private theorem top_subtraction : (6#u32) - (1#u32) = Result.ok (5#u32) := by rfl
private theorem initial_iterator :
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepU32)
      (core.ops.range.Range.Insts.DoubleEndedIterator core.iter.range.StepU32)
      { start := 0#u32, «end» := 5#u32 } = Result.ok (iteratorAt 5) := by rfl

/-- The actual generic Gf64 chain returns normally on every input, provided both
supplied callbacks meet their universal normal-result contracts. This includes
zero/unit early returns, the source leading-zero computation, every original
reverse iteration, checked arithmetic and final Frobenius call. -/
theorem normal_refines {T1 T2 : Type}
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2)
    (multiply : U64 → U64 → U64) (frobenius : U64 → U32 → U64)
    (mulNormal : MulNormal mulDict mulCallback multiply)
    (frobNormal : FrobeniusNormal frobDict frobCallback frobenius)
    (input : U64) :
    bulksketch.field.maps.inverse_with_frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField mulDict frobDict input
      mulCallback frobCallback = Result.ok (expectedResult multiply frobenius input) := by
  simp only [bulksketch.field.maps.inverse_with_frobenius,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS,
    lift, bind_ok, canonical_mask, ite_true]
  by_cases zeroInput : input = 0#u64
  · simp only [zeroInput, ite_true, expectedResult]
  · simp only [zeroInput, ite_false]
    by_cases unitInput : input = 1#u64
    · simp [unitInput, expectedResult]
    · simp only [unitInput, ite_false, target_subtraction, bind_ok, target_leading_zeros,
        length_subtraction, top_subtraction, initial_iterator]
      have complete := loop_refines mulDict frobDict mulCallback frobCallback multiply frobenius
        mulNormal frobNormal input 0 (by decide)
      change bulksketch.field.maps.inverse_with_frobenius_loop mulDict frobDict
        (iteratorAt 5) input mulCallback frobCallback (63#u32) (1#u32) input = _ at complete
      rw [complete]
      simp only [bind_ok]
      rw [frobNormal (chain multiply frobenius input 5) (1#u32)]
      simp only [bind_ok, expectedResult, zeroInput, unitInput, ite_false]

/-- Complete reachable scalar bounds: shifts use only positions0..4, doubling
stays at most62 and the appended index stays at most63 inside U32. -/
theorem source_scalar_bounds (count : Nat) (bounded : count < 5) :
    4 - count < 32 ∧ (chainIndex count).val ≤ 31 ∧
      2 * (chainIndex count).val ≤ 62 ∧ 2 * (chainIndex count).val + 1 ≤ 63 := by
  interval_cases count <;> decide +kernel

/-- Neither early return requires any callback to be total or correct. -/
theorem zero_returns_without_callbacks {T1 T2 : Type}
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2) :
    bulksketch.field.maps.inverse_with_frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField mulDict frobDict (0#u64)
      mulCallback frobCallback = Result.ok none := by
  simp only [bulksketch.field.maps.inverse_with_frobenius, lift, bind_ok,
    canonical_mask, ite_true]

/-- The unit result is equally independent of every callback's behavior. -/
theorem one_returns_without_callbacks {T1 T2 : Type}
    (mulDict : core.ops.function.Fn T1 (U64 × U64) U64)
    (frobDict : core.ops.function.Fn T2 (U64 × U32) U64)
    (mulCallback : T1) (frobCallback : T2) :
    bulksketch.field.maps.inverse_with_frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField mulDict frobDict (1#u64)
      mulCallback frobCallback = Result.ok (some (1#u64)) := by
  simp [bulksketch.field.maps.inverse_with_frobenius, lift, canonical_mask]

end BulksketchBridge.Inverse
