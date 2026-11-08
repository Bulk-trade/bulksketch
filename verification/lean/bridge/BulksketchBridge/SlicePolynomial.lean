import BulksketchBridge.SliceKernels
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.SliceKernels

open Aeneas.Std Polynomial BulksketchBridge.Algebra.Gf64
open scoped BigOperators

/-- Interpret the ascending coefficient slice in the existing GF64 quotient. -/
noncomputable def slicePolynomial (words : Slice U64) : Polynomial Field :=
  ∑ i ∈ Finset.range words.length, monomial i (toField words[i]!.bv)

theorem slicePolynomial_coeff (words : Slice U64) (index : Nat) :
    (slicePolynomial words).coeff index =
      if index < words.length then toField words[index]!.bv else 0 := by
  classical
  rw [slicePolynomial, finsetSum_coeff, Finset.sum_eq_single index]
  · by_cases bound : index < words.length
    · simp [bound]
    · have zero : words[index]! = default := by
        rw [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD, List.getElem?_eq_none (by
          simpa using Nat.le_of_not_lt bound)]
        rfl
      simp [bound, zero]
      exact toField_zero
  · intro other _ different
    simp [coeff_monomial, different]
  · intro absent
    simp [show ¬index < words.length by simpa using absent]
    exact toField_zero

theorem exact_product (original output : Slice U64) (root : U64)
    (lengthEq : output.length = original.length)
    (frame : ∀ i : Nat, i < original.length →
      output[i]! = SliceKernelChallenges.coefficientAfter original root i)
    (padding : 0 < original.length → original[original.length - 1]! = 0#u64) :
    slicePolynomial output =
      (1 + C (toField root.bv) * X) * slicePolynomial original := by
  ext i
  rw [add_mul, one_mul, mul_assoc, mul_comm X, coeff_add, coeff_C_mul,
    slicePolynomial_coeff, slicePolynomial_coeff, lengthEq]
  cases i with
  | zero =>
    rw [coeff_mul_X_zero, mul_zero, add_zero]
    by_cases active : 0 < original.length
    · simp [active, frame 0 active, SliceKernelChallenges.coefficientAfter]
    · simp [active]
  | succ i =>
    rw [coeff_mul_X, slicePolynomial_coeff]
    by_cases active : i + 1 < original.length
    · have previous : i < original.length := by omega
      rw [ite_eq_left active, ite_eq_left active, ite_eq_left previous, frame (i+1) active]
      change toField (original[i+1]!.bv ^^^ multiplyWord original[i]!.bv root.bv) = _
      rw [toField_xor, toField_mul, mul_comm (toField original[i]!.bv)]
    · have outside : ¬i + 1 < original.length := active
      rw [ite_eq_right outside, ite_eq_right outside, zero_add]
      by_cases previous : i < original.length
      · have last : i = original.length - 1 := by omega
        have lastZero := padding (by omega)
        rw [ite_eq_left previous, last, lastZero]
        rw [show toField (0#u64).bv = 0 from toField_zero, mul_zero]
      · simp [previous]

/-- The actual update computes the full product when its final slot is zero. -/
def PaddedProductRefines : Prop :=
  ∀ (Backend : Type) (kernels : bulksketch.backend.contract.BulkKernels Backend bulksketch.field.Gf64),
    (∀ left right, kernels.ArithmeticInst.mul left right =
      bulksketch.field.gf64.mul bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right) →
    ∀ (coefficients : Slice U64) (root : U64),
      (0 < coefficients.length → coefficients[coefficients.length - 1]! = 0#u64) →
      ∃ output : Slice U64,
        bulksketch.backend.contract.BulkKernels.multiply_linear.default kernels coefficients root =
          Result.ok output ∧ output.length = coefficients.length ∧
        slicePolynomial output = (1 + C (toField root.bv) * X) * slicePolynomial coefficients

theorem multiply_linear_padded_product : PaddedProductRefines := by
  intro Backend kernels nativeMul coefficients root padding
  obtain ⟨output, normal, lengthEq, frame⟩ :=
    multiply_linear_refines Backend kernels nativeMul coefficients root
  exact ⟨output, normal, lengthEq, exact_product coefficients output root lengthEq frame padding⟩

end BulksketchBridge.SliceKernels
