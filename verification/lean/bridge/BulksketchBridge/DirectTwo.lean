import BulksketchBridge.DirectTwoSpec
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.InverseUsing
import BulksketchBridge.MapsQuadratic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two

namespace BulksketchBridge.DirectTwo

open Aeneas Aeneas.Std Algebra.Gf64 bulksketch.backend.contract bulksketch.decode.direct

private theorem mask_zero (word : U64) :
    word &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
  apply U64.bv_eq_imp_eq
  simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK,
    core.num.U64.MAX, U64.rMax]

private theorem invalid_word {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (word : U64) :
    two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut fieldDictionary kernels () word =
      Result.ok (decide (word = 0#u64), ()) := by
  unfold two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  by_cases zero : word = 0#u64
  · simp [zero]
  · simp only [zero, ite_false, decide_false]
    change (do
      let mask ← Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK
      let inverted ← lift (~~~ mask)
      let masked ← lift (word &&& inverted)
      Result.ok (masked != 0#u64, ())) = _
    simp only [Bind.bind, bind_ok, lift, mask_zero]
    rfl

private theorem pair_any {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (first second : U64) :
    DirectTwoRuntime.sharedAny
        (two.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool fieldDictionary kernels)
        ⟨Array.to_slice (Array.make 2#usize [first, second]), 0⟩ () =
      Result.ok (decide (first = 0#u64 ∨ second = 0#u64),
        ⟨Array.to_slice (Array.make 2#usize [first, second]), if first = 0#u64 then 1 else 2⟩) := by
  let words := Array.to_slice (Array.make 2#usize [first, second])
  have length : words.length = 2 := rfl
  have next0 : core.slice.iter.IteratorSliceIter.next (⟨words, 0⟩ : core.slice.iter.Iter U64) =
      Result.ok (some first, ⟨words, 1⟩) := by
    have active : (0 : Nat) < (Slice.len words).val := by rw [Slice.len_val, length]; decide
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dite_eq_left active]
    rfl
  have next1 : core.slice.iter.IteratorSliceIter.next (⟨words, 1⟩ : core.slice.iter.Iter U64) =
      Result.ok (some second, ⟨words, 2⟩) := by
    have active : (1 : Nat) < (Slice.len words).val := by rw [Slice.len_val, length]; decide
    unfold core.slice.iter.IteratorSliceIter.next
    rw [dite_eq_left active]
    rfl
  change DirectTwoRuntime.sharedAny _ ⟨words, 0⟩ () = _
  unfold DirectTwoRuntime.sharedAny
  change DirectTwoRuntime.scan _ 2 ⟨words, 0⟩ () = _
  simp only [DirectTwoRuntime.scan, next0, bind_ok]
  dsimp! only
  rw [invalid_word kernels first]
  by_cases firstZero : first = 0#u64
  · simp only [firstZero, true_or, decide_true, bind_ok, ite_true]
    dsimp! only
    simp [words, firstZero]
  · simp only [firstZero, false_or, decide_false, bind_ok, ite_false, next1]
    dsimp! only
    rw [invalid_word kernels second]
    by_cases secondZero : second = 0#u64 <;> simp [secondZero, words]

private theorem normalized_equation {target solution : U64}
    (found : MapsQuadratic.expectedSolution target = some solution) :
    Square.expectedWord solution ^^^ solution = target := by
  obtain ⟨output, normal, meaning⟩ := MapsQuadratic.solve_quadratic_exact_meaning target
  rw [MapsQuadratic.solve_quadratic_refines, found] at normal
  have outputEq : output = some solution := (Result.ok_injective normal).symm
  subst output
  apply U64.bv_eq_imp_eq
  exact meaning.1

private theorem pair_index (first second : U64) :
    Array.index_usize (Array.make 2#usize [first, second]) 0#usize = Result.ok first ∧
    Array.index_usize (Array.make 2#usize [first, second]) 1#usize = Result.ok second := by
  constructor <;> simp [Array.index_usize, Array.getElem?_Usize_eq, Array.make]

/-- The original scalar two-root derivation, including its Option branches,
full equality checks and final short-circuit scan. -/
theorem direct_two_refines : ActualDirectTwoReturnsNormalizedPair := by
  intro K kernels sum third arithmetic nonzero
  have mulNormal (a b : U64) : kernels.ArithmeticInst.mul a b =
      Result.ok (Inverse.multiplyNativeWord a b) :=
    (arithmetic.1 a b).trans (native_mul_word a b)
  have squareNormal (a : U64) : kernels.ArithmeticInst.square a = Result.ok (Square.expectedWord a) :=
    (arithmetic.2.1 a).trans (Square.square_refines a)
  have inverseNormal : kernels.ArithmeticInst.inverse sum = Result.ok (some (inverseWord sum)) := by
    rw [arithmetic.2.2.1, InverseUsing.inverse_refines]
    simp only [Inverse.expectedFieldInverse, ite_eq_right nonzero, inverseWord]
  have quadraticNormal (a : U64) : kernels.ArithmeticInst.solve_quadratic a =
      Result.ok (MapsQuadratic.expectedSolution a) :=
    (arithmetic.2.2.2 a).trans (MapsQuadratic.solve_quadratic_refines a)
  have productEq : Inverse.multiplyNativeWord
      (third ^^^ Inverse.multiplyNativeWord (Square.expectedWord sum) sum) (inverseWord sum) =
        productWord sum third := rfl
  have targetEq : Inverse.multiplyNativeWord (productWord sum third)
      (Square.expectedWord (inverseWord sum)) = targetWord sum third := rfl
  unfold two expectedPair
  simp only [Bind.bind, inverseNormal, bind_ok, core.option.Option.expect, Result.ofOption,
    squareNormal, mulNormal, lift, productEq, targetEq]
  by_cases zero : productWord sum third = 0#u64
  · simp only [zero, ite_true]
  · simp only [zero, ite_false, quadraticNormal, bind_ok]
    cases found : MapsQuadratic.expectedSolution (targetWord sum third) with
    | none =>
      simp only [bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok,
        bulksketch.core.option.Option.Insts.CoreOpsTry_traitFromResidualOptionNever.from_residual]
      rfl
    | some solution =>
      have equation := normalized_equation found
      simp only [bulksketch.core.option.Option.Insts.CoreOpsTry_traitTry.branch, bind_ok]
      dsimp! only
      simp only [mask_zero, bne_self_eq_false, Bool.false_eq_true, ite_false, equation]
      let first := Inverse.multiplyNativeWord sum solution
      let second := first ^^^ sum
      have reads := pair_index (Inverse.multiplyNativeWord sum solution)
        (Inverse.multiplyNativeWord sum solution ^^^ sum)
      simp only [reads.1, reads.2, bind_ok]
      by_cases same : first = second
      · simpa only [first, second] using (show
          (if first = second then Result.ok (none : Option Pair) else _) =
            Result.ok (if first = second ∨ first = 0#u64 ∨ second = 0#u64 then none
              else some { roots := Array.make 2#usize [first, second] }) from by
              simp only [same, ite_true, true_or])
      · simp only [show Inverse.multiplyNativeWord sum solution ≠
          Inverse.multiplyNativeWord sum solution ^^^ sum from same, ite_false, false_or,
          core.slice.Slice.iter, bind_ok, pair_any]
        dsimp! only
        by_cases bad : first = 0#u64 ∨ second = 0#u64
        · simp only [show Inverse.multiplyNativeWord sum solution = 0#u64 ∨
            Inverse.multiplyNativeWord sum solution ^^^ sum = 0#u64 from bad,
            decide_true, ite_true]
        · simp only [show ¬ (Inverse.multiplyNativeWord sum solution = 0#u64 ∨
            Inverse.multiplyNativeWord sum solution ^^^ sum = 0#u64) from bad,
            decide_false, Bool.false_eq_true, ite_false]

private theorem inverseWord_field (sum : U64) :
    toField (inverseWord sum).bv = (toField sum.bv)⁻¹ :=
  wordFieldEquiv.apply_symm_apply _

private theorem productWord_field (sum third : U64) :
    toField (productWord sum third).bv =
      (toField third.bv + toField sum.bv ^ 3) * (toField sum.bv)⁻¹ := by
  change toField (multiplyWord
    (third.bv ^^^ multiplyWord (BulksketchProofs.Field.Period.squareWord sum.bv) sum.bv)
    (inverseWord sum).bv) = _
  rw [toField_mul, toField_xor, toField_mul, toField_square, inverseWord_field, pow_succ _ 2]

private theorem targetWord_field (sum third : U64) :
    toField (targetWord sum third).bv =
      toField (productWord sum third).bv * (toField sum.bv)⁻¹ ^ 2 := by
  change toField (multiplyWord (productWord sum third).bv
    (BulksketchProofs.Field.Period.squareWord (inverseWord sum).bv)) = _
  rw [toField_mul, toField_square, inverseWord_field]

private theorem binary_cube_sum {K : Type*} [_root_.Field K] [CharP K 2] (first second : K) :
    first ^ 3 + second ^ 3 = (first + second) ^ 3 + (first + second) * (first * second) := by
  symm
  calc
    (first + second) ^ 3 + (first + second) * (first * second) =
        first ^ 3 + second ^ 3 + 2 * (2 * (first ^ 2 * second + first * second ^ 2)) := by ring
    _ = first ^ 3 + second ^ 3 := by rw [CharTwo.two_eq_zero, zero_mul, add_zero]

theorem direct_two_sound : ActualDirectTwoSound := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  intro K kernels sum third pair arithmetic nonzero returned
  have expected : expectedPair sum third = some pair :=
    Result.ok_injective ((direct_two_refines kernels sum third arithmetic nonzero).symm.trans returned)
  unfold expectedPair at expected
  by_cases productZero : productWord sum third = 0#u64
  · simp [productZero] at expected
  · simp only [productZero, ite_false] at expected
    cases found : MapsQuadratic.expectedSolution (targetWord sum third) with
    | none => simp [found] at expected
    | some solution =>
      simp only [found, Option.bind_eq_bind, Option.bind_some] at expected
      let first := Inverse.multiplyNativeWord sum solution
      let second := first ^^^ sum
      change (if first = second ∨ first = 0#u64 ∨ second = 0#u64 then none else
        some { roots := Array.make 2#usize [first, second] }) = some pair at expected
      by_cases invalid : first = second ∨ first = 0#u64 ∨ second = 0#u64
      · simp [invalid] at expected
      · rw [ite_eq_right invalid] at expected
        have pairEq : pair = { roots := Array.make 2#usize [first, second] } :=
          (Option.some.inj expected).symm
        have sumNonzero : toField sum.bv ≠ 0 := by
          intro zero
          apply nonzero
          apply U64.bv_eq_imp_eq
          apply toField_injective
          exact zero.trans toField_zero.symm
        have firstField : toField first.bv = toField sum.bv * toField solution.bv := toField_mul _ _
        have secondField : toField second.bv = toField first.bv + toField sum.bv := toField_xor _ _
        have sumEq : toField first.bv + toField second.bv = toField sum.bv := by
          rw [secondField, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
        have inverseSquare : toField sum.bv ^ 2 * (toField sum.bv)⁻¹ ^ 2 = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ sumNonzero, one_pow]
        have equation := congrArg (fun word : U64 => toField word.bv) (normalized_equation found)
        change toField (BulksketchProofs.Field.Period.squareWord solution.bv ^^^ solution.bv) =
          toField (targetWord sum third).bv at equation
        rw [toField_xor, toField_square, targetWord_field] at equation
        have productEq : toField first.bv * toField second.bv = toField (productWord sum third).bv := by
          calc
            toField first.bv * toField second.bv =
                toField sum.bv ^ 2 * (toField solution.bv ^ 2 + toField solution.bv) := by
                  rw [secondField, firstField]
                  ring
            _ = toField (productWord sum third).bv *
                  (toField sum.bv ^ 2 * (toField sum.bv)⁻¹ ^ 2) := by rw [equation]; ring
            _ = _ := by rw [inverseSquare, mul_one]
        refine ⟨first, second, by rw [pairEq], fun same => invalid (Or.inl same),
          fun zero => invalid (Or.inr (Or.inl zero)), fun zero => invalid (Or.inr (Or.inr zero)),
          sumEq, ?_⟩
        rw [binary_cube_sum, sumEq, productEq, productWord_field]
        calc
          toField sum.bv ^ 3 + toField sum.bv *
              ((toField third.bv + toField sum.bv ^ 3) * (toField sum.bv)⁻¹) =
              toField sum.bv ^ 3 + (toField third.bv + toField sum.bv ^ 3) *
                (toField sum.bv * (toField sum.bv)⁻¹) := by ring
          _ = _ := by
            rw [mul_inv_cancel₀ sumNonzero, mul_one, add_left_comm,
              CharTwo.add_self_eq_zero, add_zero]

end BulksketchBridge.DirectTwo
