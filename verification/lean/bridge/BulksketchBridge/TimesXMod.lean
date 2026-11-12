import BulksketchBridge.TimesXModSpec
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.ReconstructionLoop
import BulksketchBridge.SlicePolynomial
import Mathlib.Tactic.Ring
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two

namespace BulksketchBridge.TimesXMod

open Aeneas Aeneas.Std
set_option maxRecDepth 4096

open BulksketchBridge DenseCoefficient
open bulksketch.backend.contract

/-- Exact original prelude and scale-XOR call. The shifted coefficients
are the old prefix shifted right by one slot, with a zero constant. -/
theorem times_x_mod_refines : ActualTimesXMod := by
  intro F K field kernels coefficients modulus positive room
  obtain ⟨last, subtracted, lastValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := Slice.len coefficients) (y := 1#usize) (by
      rw [Slice.len_val]
      change 1 ≤ coefficients.length
      omega))
  rw [Slice.len_val] at lastValue
  change last.val = coefficients.length - 1 at lastValue
  obtain ⟨leading, read, value⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_usize_spec coefficients last (by omega))
  have bounded : last.val < coefficients.val.length := by
    change last.val < coefficients.length
    omega
  have leadingExact : leading = coefficients[coefficients.length - 1]! := by
    rw [value, Slice.getElem!_Nat_eq, ← lastValue]
    exact List.Inhabited_getElem_eq_getElem! _ _ bounded
  let shifted := coefficients.setSlice! 1 (coefficients.val.take last.val)
  have shiftedLength : shifted.length = coefficients.length := Slice.setSlice!_length _ _ _
  have update := Reconstruction.update_normal shifted 0#usize 0#u64 (by
    change 0 < shifted.length
    omega)
  have slice := RebuiltLfsr.shared_prefix_normal modulus (Slice.len coefficients) (by simpa using room)
  unfold bulksketch.poly.dense.times_x_mod
  simp only [subtracted, read, bind_ok, bulksketch.core.slice.Slice.copy_within,
    bulksketch.core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds,
    bulksketch.core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.start_bound,
    bulksketch.core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.end_bound]
  have fits : last.val ≤ coefficients.length ∧ (1#usize : Usize).val + last.val ≤ coefficients.length := by
    change last.val ≤ coefficients.length ∧ 1 + last.val ≤ coefficients.length
    omega
  rw [ite_eq_left fits]
  simp only [bind_ok, show (1#usize : Usize).val = 1 from rfl]
  rw [update]
  simp only [bind_ok, Slice.index_SliceIndexRangeToUsizeSliceInst, slice, Slice.len_val,
    leadingExact]
  simp only [shifted, lastValue]
  rfl

open SliceKernels Algebra.Gf64 Polynomial

theorem shifted_length (words : Slice U64) : (shiftedWords words).length = words.length := by
  simp only [shiftedWords, Slice.setAtNat_length, Slice.setSlice!_length]

theorem shifted_zero (words : Slice U64) (positive : 0 < words.length) :
    (shiftedWords words)[0]! = 0#u64 := by
  unfold shiftedWords
  rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq]
  rwa [Slice.setSlice!_length]

theorem shifted_succ (words : Slice U64) (i : Nat) (inside : i + 1 < words.length) :
    (shiftedWords words)[i + 1]! = words[i]! := by
  have takeLength : (words.val.take (words.length - 1)).length = words.length - 1 := by
    rw [List.length_take, Nat.min_eq_left]
    change words.length - 1 ≤ words.length
    omega
  have room : i + 1 < words.val.length := inside
  unfold shiftedWords
  simp only [Slice.getElem!_Nat_eq]
  rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega), Slice.setSlice!_val,
    List.getElem!_setSlice!_middle _ _ _ _ (by rw [takeLength]; omega), Nat.add_sub_cancel_right]
  simpa only [List.slice, List.drop_zero, Nat.sub_zero, Nat.zero_add] using
    List.getElem!_slice 0 (words.length - 1) i words.val
      ⟨by change words.length - 1 ≤ words.length; omega, by omega⟩

/-- The exact overlapping move and zeroing remove only the outgoing high
coefficient from multiplication by X. -/
theorem shift_polynomial (words : Slice U64) (positive : 0 < words.length) :
    X * slicePolynomial words = slicePolynomial (shiftedWords words) +
      monomial words.length (toField words[words.length - 1]!.bv) := by
  ext i
  rw [coeff_add, slicePolynomial_coeff, shifted_length, coeff_monomial]
  cases i with
  | zero =>
    rw [coeff_X_mul_zero, ite_eq_left positive, shifted_zero words positive, show toField (0#u64).bv = 0 from toField_zero,
      ite_eq_right (by omega : words.length ≠ 0), add_zero]
  | succ i =>
    rw [coeff_X_mul, slicePolynomial_coeff]
    by_cases inside : i + 1 < words.length
    · rw [ite_eq_left (by omega : i < words.length), ite_eq_left inside, shifted_succ words i inside,
        ite_eq_right (by omega : words.length ≠ i + 1), add_zero]
    · rw [ite_eq_right inside, zero_add]
      by_cases final : words.length = i + 1
      · rw [ite_eq_left final, ite_eq_left (by omega : i < words.length)]
        have index : words.length - 1 = i := by omega
        rw [index]
      · rw [ite_eq_right final, ite_eq_right (by omega : ¬ i < words.length)]

theorem monic_words (modulus : Slice U64) (degree : Nat)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64) :
    slicePolynomial modulus = slicePolynomial (prefixSlice modulus degree) + monomial degree 1 := by
  ext i
  rw [coeff_add, coeff_monomial, slicePolynomial_coeff, prefix_coeff _ _ _ (by omega), shape]
  by_cases lower : i < degree
  · rw [ite_eq_left lower, ite_eq_left (by omega : i < degree + 1),
      ite_eq_right (by omega : degree ≠ i), add_zero]
  · by_cases equal : i = degree
    · subst i
      rw [ite_eq_left (by omega : degree < degree + 1), ite_eq_right lower,
        ite_eq_left rfl, zero_add, monic]
      exact toField_one
    · rw [ite_eq_right lower, ite_eq_right (by omega : ¬i < degree + 1),
        ite_eq_right (Ne.symm equal), zero_add]

/-- The admitted source step returns the exact reduced degree-d frame.
The returned polynomial represents X times the original in the quotient
by the native monic modulus. -/
theorem times_x_mod_polynomial : TimesXModPolynomial := by
  intro K kernels arithmetic coefficients modulus positive shape monic
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  let degree := coefficients.length
  let shifted := shiftedWords coefficients
  let low := prefixSlice modulus degree
  let high := coefficients[degree - 1]!
  have shiftedLen : shifted.length = degree := shifted_length _
  have lowLen : low.length = degree :=
    (RebuiltLfsr.prefix_length _ _).trans (Nat.min_eq_left (by omega))
  obtain ⟨output, normal, outLen, outputWord⟩ := arithmetic shifted low high (shiftedLen.trans lowLen.symm)
  refine ⟨output, ?_, outLen.trans shiftedLen, ?_⟩
  · rw [times_x_mod_refines _ _ _ _ positive (by omega)]
    exact normal
  have polynomialOut :
      slicePolynomial output = slicePolynomial shifted + C (toField high.bv) * slicePolynomial low := by
    ext i
    rw [coeff_add, coeff_C_mul, slicePolynomial_coeff, slicePolynomial_coeff, slicePolynomial_coeff,
      outLen, shiftedLen, lowLen]
    by_cases active : i < degree
    · rw [ite_eq_left active, outputWord i (by omega), ite_eq_left active, ite_eq_left active]
      change toField (shifted[i]!.bv ^^^ multiplyWord high.bv low[i]!.bv) = _
      rw [toField_xor, toField_mul]
    · simp only [active, ite_false, mul_zero, add_zero]
  refine ⟨C (toField high.bv), ?_⟩
  rw [shift_polynomial coefficients positive, polynomialOut, monic_words modulus degree shape monic]
  change (slicePolynomial shifted + monomial degree (toField high.bv)) +
    (slicePolynomial shifted + C (toField high.bv) * slicePolynomial low) =
      (slicePolynomial low + monomial degree 1) * C (toField high.bv)
  simp only [← C_mul_X_pow_eq_monomial, map_one, one_mul]
  calc
    _ = (slicePolynomial shifted + slicePolynomial shifted) +
          (slicePolynomial low + X ^ degree) * C (toField high.bv) := by ring
    _ = _ := by rw [CharTwo.add_self_eq_zero, zero_add]

end BulksketchBridge.TimesXMod
