import BulksketchBridge.Inverse
import BulksketchBridge.InverseFieldSpec
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.Algebra.WordEquiv
import BulksketchBridge.Algebra.InversePower

/-! Algebraic meaning of the original, now normally terminating, inversion
chain. The coefficient-word interpretation is the independently constructed
Mathlib quotient-field map. No inverse law is assumed of native arithmetic. -/

namespace BulksketchBridge.Inverse

open Aeneas Aeneas.Std
open BulksketchBridge.Algebra.Gf64

theorem chain_index_bound (count : Nat) (bounded : count ≤ 5) :
    (chainIndex count).val = 2 ^ (count + 1) - 1 ∧ (chainIndex count).val ≤ 63 := by
  interval_cases count <;> decide +kernel

private theorem step_exponent (value : Field) (index : Nat) :
    ((value ^ (2 ^ index - 1)) ^ (2 ^ index) * value ^ (2 ^ index - 1)) ^ 2 * value =
      value ^ (((2 ^ index - 1) * 2 ^ index + (2 ^ index - 1)) * 2 + 1) := by
  rw [← pow_mul, ← pow_add, ← pow_mul, pow_succ]

/-- The exact word prefix is a^(2^k-1) at every one of the six reachable k.
This theorem proves the mathematical purpose of each original iteration. -/
theorem chain_meaning (input : U64) (count : Nat) (bounded : count ≤ 5) :
    toField (chain multiplyNativeWord frobeniusNativeWord input count).bv =
      toField input.bv ^ (2 ^ (2 ^ (count + 1) - 1) - 1) := by
  induction count with
  | zero => simp [chain]
  | succ count inductionHypothesis =>
    have previous := inductionHypothesis (by omega)
    have stepBound : count < 5 := by omega
    rw [chain]
    change toField (multiplyWord
      (BulksketchProofs.Field.Period.iterateSquare (1#u32).val
        (multiplyWord
          (BulksketchProofs.Field.Period.iterateSquare (chainIndex count).val
            (chain multiplyNativeWord frobeniusNativeWord input count).bv)
          (chain multiplyNativeWord frobeniusNativeWord input count).bv)) input.bv) = _
    rw [toField_mul, toField_iterateSquare, toField_mul, toField_iterateSquare, previous]
    rw [(chain_index_bound count (by omega)).1]
    simp only [show (1#u32).val = 1 from rfl, pow_one]
    rw [step_exponent]
    congr 1
    interval_cases count <;> decide +kernel

/-- The complete non-early-return word denotes the actual field inverse. -/
theorem completed_chain_inverse (input : U64) :
    toField (frobeniusNativeWord
      (chain multiplyNativeWord frobeniusNativeWord input 5) (1#u32)).bv =
        (toField input.bv)⁻¹ := by
  change toField (BulksketchProofs.Field.Period.iterateSquare (1#u32).val
    (chain multiplyNativeWord frobeniusNativeWord input 5).bv) = _
  rw [toField_iterateSquare, chain_meaning input 5 (by decide)]
  change (toField input.bv ^ (2 ^ 63 - 1)) ^ 2 = _
  rw [← pow_mul]
  convert word_inverse_power input.bv using 1

theorem expected_result_is_field_inverse (input : U64) :
    expectedResult multiplyNativeWord frobeniusNativeWord input = expectedFieldInverse input := by
  unfold expectedResult expectedFieldInverse
  split
  · rfl
  · split
    · rename_i unitInput
      subst input
      apply congrArg some
      apply U64.bv_eq_imp_eq
      apply toField_injective
      change toField (1 : BitVec 64) = toField (wordFieldEquiv.symm
        (toField (1 : BitVec 64))⁻¹)
      rw [toField_one, inv_one]
      exact (wordFieldEquiv.apply_symm_apply _).symm
    · apply congrArg some
      apply U64.bv_eq_imp_eq
      apply toField_injective
      rw [completed_chain_inverse]
      exact (wordFieldEquiv.apply_symm_apply _).symm

end BulksketchBridge.Inverse
