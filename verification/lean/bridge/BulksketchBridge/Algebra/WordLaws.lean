import BulksketchBridge.Algebra.WordOps
import BulksketchBridge.Algebra.WordSquare
import BulksketchBridge.Algebra.WordChallenges

/-! Field laws transported through the proved injective polynomial-basis map.
The operations are the complete native word models, rather than the numeric
addition and multiplication of Lean's standard BitVec type. -/
namespace BulksketchBridge.Algebra.Gf64

open BulksketchProofs.Field

theorem multiplyWord_comm (left right : BitVec 64) :
    multiplyWord left right = multiplyWord right left := by
  apply toField_injective
  rw [toField_mul, toField_mul, mul_comm]

theorem multiplyWord_assoc (a b c : BitVec 64) :
    multiplyWord (multiplyWord a b) c = multiplyWord a (multiplyWord b c) := by
  apply toField_injective
  simp only [toField_mul, mul_assoc]

@[simp] theorem multiplyWord_one (input : BitVec 64) : multiplyWord input 1 = input := by
  apply toField_injective
  rw [toField_mul, toField_one, mul_one]

@[simp] theorem one_multiplyWord (input : BitVec 64) : multiplyWord 1 input = input := by
  rw [multiplyWord_comm, multiplyWord_one]

@[simp] theorem multiplyWord_zero (input : BitVec 64) : multiplyWord input 0 = 0 := by
  apply toField_injective
  rw [toField_mul, toField_zero, mul_zero]

@[simp] theorem zero_multiplyWord (input : BitVec 64) : multiplyWord 0 input = 0 := by
  rw [multiplyWord_comm, multiplyWord_zero]

theorem multiplyWord_xor (a b c : BitVec 64) :
    multiplyWord a (b ^^^ c) = multiplyWord a b ^^^ multiplyWord a c := by
  apply toField_injective
  simp only [toField_mul, toField_xor, mul_add]

theorem xor_multiplyWord (a b c : BitVec 64) :
    multiplyWord (a ^^^ b) c = multiplyWord a c ^^^ multiplyWord b c := by
  apply toField_injective
  simp only [toField_mul, toField_xor, add_mul]

theorem squareWord_eq_product (input : BitVec 64) :
    Period.squareWord input = multiplyWord input input := by
  apply toField_injective
  rw [toField_square, toField_mul, pow_two]

theorem arithmetic_field_laws : WordChallenges.ArithmeticFieldLaws := by
  intro a b c
  exact ⟨multiplyWord_comm a b, multiplyWord_assoc a b c, multiplyWord_one a,
    one_multiplyWord a, multiplyWord_zero a, zero_multiplyWord a, multiplyWord_xor a b c,
    xor_multiplyWord a b c, squareWord_eq_product a⟩

end BulksketchBridge.Algebra.Gf64
