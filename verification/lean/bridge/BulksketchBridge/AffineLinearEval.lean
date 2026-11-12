import BulksketchBridge.AffineLinearEvalSpec
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.AffineLinearEval

open Aeneas Aeneas.Std Aeneas.Std.WP
open BulksketchBridge.Algebra.Gf64
open bulksketch.backend.contract bulksketch.decode.affine
open scoped BigOperators

private abbrev Iter := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter U64)

private def iterAt (linear : Slice U64) (count : Usize) : Iter :=
  { iter := ⟨linear, count.val⟩, count := count }

private theorem value_step (linear : Slice U64) (input : U64) (count : Nat)
    (active : count < linear.length) :
    linearValueFrom linear input count =
      toField linear[count]!.bv * toField input.bv ^ (2 ^ count) +
        linearValueFrom linear input (count + 1) := by
  simp only [linearValueFrom,
    show linear.length - count = (linear.length - (count + 1)) + 1 by omega,
    Finset.sum_range_succ', Nat.add_zero]
  rw [add_comm]
  apply congrArg (fun value : Field =>
    toField linear[count]!.bv * toField input.bv ^ (2 ^ count) + value)
  apply Finset.sum_congr rfl
  intro offset _
  rw [show count + (offset + 1) = count + 1 + offset by omega]

private theorem iter_step (linear : Slice U64) (count : Usize)
    (active : count.val < linear.length) :
    ∃ advanced : Usize,
      count + 1#usize = Result.ok advanced ∧ advanced.val = count.val + 1 ∧
      core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count) =
        Result.ok (some (count, linear[count.val]!), iterAt linear advanced) := by
  have one : (1#usize).val = 1 := by simp
  have safe : count.val + (1#usize).val ≤ Usize.max := by
    have bound := Slice.length_ineq linear
    rw [one]
    exact (Nat.succ_le_of_lt active).trans bound
  obtain ⟨advanced, addNormal, addPost⟩ := RawMulTable.normal_of_spec _ _ (Usize.add_spec (x := count) (y := 1#usize) safe)
  have advancedValue : advanced.val = count.val + 1 := by simpa only [one] using addPost
  refine ⟨advanced, addNormal, advancedValue, ?_⟩
  have inner : core.slice.iter.IteratorSliceIter.next ⟨linear, count.val⟩ =
      Result.ok (some linear[count.val]!, ⟨linear, count.val + 1⟩) := by
    have step : count.val < (Slice.len linear).val := by rwa [Slice.len_val]
    simp only [core.slice.iter.IteratorSliceIter.next, step, _root_.dite_true]
    exact congrArg (fun item => Result.ok (some item, (⟨linear, count.val + 1⟩ : core.slice.iter.Iter U64)))
      (Slice.Inhabited_getElem_eq_getElem! linear count.val active)
  have post := core.iter.adapters.enumerate.IteratorEnumerate.next_some_spec
    (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count)
    linear[count.val]! ⟨linear, count.val + 1⟩ (by
      change WP.spec (core.slice.iter.IteratorSliceIter.next _) _
      simp only [iterAt, inner, spec_ok, and_self]) (by simpa only [iterAt, one] using safe)
  obtain ⟨⟨opt, state⟩, normal, rfl, stateIter, stateVal⟩ := RawMulTable.normal_of_spec _ _ post
  have countEq : state.count = advanced := UScalar.eq_of_val_eq (stateVal.trans advancedValue.symm)
  have stateEq : state = iterAt linear advanced := by
    cases state
    simp_all [iterAt]
  rw [normal, stateEq]
  rfl

private theorem iter_done (linear : Slice U64) (count : Usize)
    (stopped : linear.length ≤ count.val) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count) =
      Result.ok (none, iterAt linear count) := by
  have inactive : ¬ count.val < (Slice.len linear).val := by rw [Slice.len_val]; omega
  have inner : core.slice.iter.IteratorSliceIter.next (⟨linear, count.val⟩ : core.slice.iter.Iter U64) =
      Result.ok (none, ⟨linear, count.val⟩) := by
    simp only [core.slice.iter.IteratorSliceIter.next, inactive, _root_.dite_false]
  have post := core.iter.adapters.enumerate.IteratorEnumerate.next_none_spec
    (core.iter.traits.iterator.IteratorSliceIter U64) (iterAt linear count)
    ⟨linear, count.val⟩ (by
      change WP.spec (core.slice.iter.IteratorSliceIter.next _) _
      simp only [iterAt, inner, spec_ok, and_self])
  obtain ⟨⟨opt, state⟩, normal, rfl, stateIter, stateCount⟩ := RawMulTable.normal_of_spec _ _ post
  have stateEq : state = iterAt linear count := by
    cases state
    simp_all [iterAt]
  rw [normal, stateEq]

private theorem loop_refines {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (arithmetic : CorrectArithmetic kernels) (linear : Slice U64) (input : U64)
    (count : Usize) (x accumulator : U64)
    (xMeaning : count.val < linear.length → toField x.bv = toField input.bv ^ (2 ^ count.val)) :
    ∃ output : U64,
      linear_eval_loop fieldDictionary kernels (iterAt linear count) linear x accumulator = Result.ok output ∧
      toField output.bv = toField accumulator.bv + linearValueFrom linear input count.val := by
  suffices ∀ remaining (count : Usize) (x accumulator : U64),
      linear.length - count.val = remaining →
      (count.val < linear.length → toField x.bv = toField input.bv ^ (2 ^ count.val)) →
      ∃ output : U64,
        linear_eval_loop fieldDictionary kernels (iterAt linear count) linear x accumulator = Result.ok output ∧
        toField output.bv = toField accumulator.bv + linearValueFrom linear input count.val from
    this (linear.length - count.val) count x accumulator rfl xMeaning
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining inductionHypothesis =>
    intro count x accumulator remainingEq xMeaning
    by_cases active : count.val < linear.length
    · obtain ⟨advanced, incrementNormal, advancedValue, nextNormal⟩ := iter_step linear count active
      let product : U64 := ⟨multiplyWord linear[count.val]!.bv x.bv⟩
      let accNext := accumulator ^^^ product
      let xNext := if advanced = Slice.len linear then x else Square.expectedWord x
      have productNormal : kernels.ArithmeticInst.mul linear[count.val]! x = Result.ok product :=
        (arithmetic.1 _ _).trans (native_mul_word _ _)
      have squareNormal : kernels.ArithmeticInst.square x = Result.ok (Square.expectedWord x) :=
        (arithmetic.2 _).trans (Square.square_refines _)
      have bodyNormal : linear_eval_loop.body fieldDictionary kernels linear (iterAt linear count)
          x accumulator = Result.ok (ControlFlow.cont (iterAt linear advanced, xNext, accNext)) := by
        simp only [linear_eval_loop.body, nextNormal, bind_ok]
        change (do
          let value ← kernels.ArithmeticInst.mul linear[count.val]! x
          let out ← lift (accumulator ^^^ value)
          let next ← count + 1#usize
          if next != Slice.len linear then do
            let squared ← kernels.ArithmeticInst.square x
            Result.ok (ControlFlow.cont (iterAt linear advanced, squared, out))
          else Result.ok (ControlFlow.cont (iterAt linear advanced, x, out))) = _
        simp only [Bind.bind, productNormal, incrementNormal, bind_ok, lift, xNext, accNext]
        by_cases final : advanced = Slice.len linear <;>
          simp only [bne_iff_ne, ne_eq, final, not_true_eq_false, not_false_eq_true,
            ite_true, ite_false, squareNormal, bind_ok]
      have nextMeaning (nextActive : advanced.val < linear.length) :
          toField xNext.bv = toField input.bv ^ (2 ^ advanced.val) := by
        have notFinal : advanced ≠ Slice.len linear := by
          intro final
          rw [final, Slice.len_val] at nextActive
          omega
        simp only [xNext, ite_eq_right notFinal]
        change toField (BulksketchProofs.Field.Period.squareWord x.bv) = _
        rw [toField_square, xMeaning active, advancedValue, pow_succ (2 : Nat) count.val, ← pow_mul]
      obtain ⟨output, loopNormal, meaning⟩ := inductionHypothesis (linear.length - advanced.val)
        (by omega) advanced xNext accNext rfl nextMeaning
      refine ⟨output, ?_, ?_⟩
      · unfold linear_eval_loop loop
        dsimp only
        rw [bodyNormal]
        simpa only [linear_eval_loop, bind_ok] using loopNormal
      · rw [meaning, value_step linear input count.val active, advancedValue]
        change toField (accumulator.bv ^^^ product.bv) + _ = _
        rw [toField_xor]
        change toField accumulator.bv + toField (multiplyWord linear[count.val]!.bv x.bv) + _ = _
        rw [toField_mul, xMeaning active, add_assoc]
    · have nextNormal := iter_done linear count (by omega)
      refine ⟨accumulator, ?_, ?_⟩
      · unfold linear_eval_loop loop
        dsimp only
        simp only [linear_eval_loop.body, nextNormal, bind_ok]
        dsimp! only
        simp only [bind_ok]
      · simp [linearValueFrom, show linear.length - count.val = 0 by omega]

theorem linear_eval_refines : ActualLinearEvaluation := by
  intro Backend kernels linear input arithmetic
  obtain ⟨output, normal, meaning⟩ := loop_refines kernels arithmetic linear input
    0#usize input 0#u64 (by intro _; simp)
  refine ⟨output, ?_, ?_⟩
  · have initialCount : (0#usize).val = 0 := by simp
    simpa only [linear_eval, core.slice.Slice.iter,
      core.iter.traits.iterator.Iterator.enumerate.trait_default,
      core.iter.traits.iterator.Iterator.enumerate.default, bind_ok, iterAt, initialCount] using normal
  · have initialZero : toField (0#u64).bv = 0 := toField_zero
    simpa only [initialZero, zero_add, UScalar.ofNatCore_val_eq] using meaning

end BulksketchBridge.AffineLinearEval
