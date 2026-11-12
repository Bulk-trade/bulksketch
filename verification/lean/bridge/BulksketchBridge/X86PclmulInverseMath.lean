import BulksketchBridge.InverseFieldSpec
import BulksketchBridge.Algebra.WordNative
import BulksketchBridge.Algebra.InversePower

namespace BulksketchBridge.X86Pclmul

open Aeneas.Std Algebra.Gf64
open Inverse (multiplyNativeWord frobeniusNativeWord expectedFieldInverse)

/-- The word-level fast chain, with the same exponents and multiplication
order as the x86 branch. Each operation uses the verified GF64 value model. -/
def inverseChainWord (input : U64) : U64 :=
  let t2 := multiplyNativeWord (multiplyNativeWord input input) input
  let t3 := multiplyNativeWord (multiplyNativeWord t2 t2) input
  let t6 := multiplyNativeWord (frobeniusNativeWord t3 3#u32) t3
  let t7 := multiplyNativeWord (multiplyNativeWord t6 t6) input
  let t14 := multiplyNativeWord (frobeniusNativeWord t7 7#u32) t7
  let t21 := multiplyNativeWord (frobeniusNativeWord t14 7#u32) t7
  let t42 := multiplyNativeWord (frobeniusNativeWord t21 21#u32) t21
  let t63 := multiplyNativeWord (frobeniusNativeWord t42 21#u32) t21
  multiplyNativeWord t63 t63

private theorem mul_field (a b : U64) :
    toField (multiplyNativeWord a b).bv = toField a.bv * toField b.bv :=
  toField_mul a.bv b.bv

private theorem frobenius_field (a : U64) (power : U32) :
    toField (frobeniusNativeWord a power).bv = toField a.bv ^ (2 ^ power.val) :=
  toField_iterateSquare power.val a.bv

theorem inverse_chain_exponent (input : U64) :
    toField (inverseChainWord input).bv = toField input.bv ^ ((2 ^ 64 : Nat) - 2) := by
  simp only [inverseChainWord, mul_field, frobenius_field,
    show (3#u32).val = 3 from rfl, show (7#u32).val = 7 from rfl,
    show (21#u32).val = 21 from rfl, ← pow_two, ← pow_mul, ← pow_add, ← pow_succ]
  congr 1

/-- Exact correspondence with the same field-inverse spec used by the
original scalar inverse. The zero guard belongs to the source method. -/
theorem inverse_chain_field (input : U64) (nonzero : input ≠ 0#u64) :
    some (inverseChainWord input) = expectedFieldInverse input := by
  rw [expectedFieldInverse, ite_eq_right nonzero]
  apply congrArg some
  apply U64.bv_eq_imp_eq
  apply toField_injective
  rw [inverse_chain_exponent, word_inverse_power]
  exact (wordFieldEquiv.apply_symm_apply _).symm

end BulksketchBridge.X86Pclmul
