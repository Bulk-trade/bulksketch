import BulksketchBridge.Algebra.WordNativeChallenges
import BulksketchBridge.Algebra.Word
import BulksketchBridge.Algebra.Trace
import BulksketchBridge.RawMul
import BulksketchBridge.Square
import BulksketchBridge.FrobeniusPeriod

/-! Composition with the unchanged generated application bodies. The word map
uses Mathlib's polynomial quotient and its independently proved field instance.
The frontend/runtime/compiler/machine boundary remains explicit. -/

namespace BulksketchBridge.Algebra.Gf64

open Aeneas Aeneas.Std

/-- Every actual reduction computes the exact polynomial quotient class. -/
theorem native_reduce_is_quotient : WordNativeChallenges.actualReductionIsQuotientRemainder := by
  intro product
  obtain ⟨output, normal, exactBits, _⟩ := Gf64Reduce.reduce_refines product
  refine ⟨output, normal, ?_⟩
  rw [exactBits]
  exact toField_reduce product.lo.bv product.hi.bv

/-- A complete-word normal-output equation, useful for supplying native callbacks. -/
theorem native_mul_word (left right : U64) :
    bulksketch.field.gf64.mul
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right =
        Result.ok (⟨multiplyWord left.bv right.bv⟩ : U64) := by
  obtain ⟨output, normal, exactBits, _⟩ :=
    Gf64Reduce.reduce_refines (RawMul.expectedProduct left right)
  have exactWord : output = (⟨multiplyWord left.bv right.bv⟩ : U64) := by
    apply U64.bv_eq_imp_eq
    exact exactBits
  rw [bulksketch.field.gf64.mul, RawMul.raw_mul_refines]
  simpa only [bind_ok, exactWord] using normal

/-- Native multiplication, now with field multiplication semantics. -/
theorem native_mul_is_field : WordNativeChallenges.actualMultiplicationIsFieldMultiplication := by
  intro left right
  exact ⟨⟨multiplyWord left.bv right.bv⟩, native_mul_word left right,
    toField_mul left.bv right.bv⟩

/-- The actual source square is Mathlib's field square on every input. -/
theorem native_square_is_field : WordNativeChallenges.actualSquareIsFieldSquare := by
  intro input
  exact ⟨Square.expectedWord input, Square.square_refines input, toField_square input.bv⟩

/-- The native U32 request denotes its full unmodded field-power exponent. -/
theorem native_frobenius_is_field : WordNativeChallenges.actualFrobeniusIsFieldPower := by
  intro input power
  refine ⟨⟨BulksketchProofs.Field.Period.iterateSquare power.val input.bv⟩,
    FrobeniusPeriod.native_unmodded_refines input power, ?_⟩
  exact toField_iterateSquare power.val input.bv

end BulksketchBridge.Algebra.Gf64
