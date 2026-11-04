import Arithmetic.Funs
import BulksketchBridge.Spread
import BulksketchBridge.SquareSpec
import BulksketchBridge.Gf64Reduce
import BulksketchProofs.Field.Reduction

/-!
# Actual generated GF64 square body

The application definition is imported unchanged from the canonical native
extraction. Proofs use the real extracted Gf64 dictionary and retain the
existing frontend/scalar-runtime/compiler/machine trust boundary.
-/

namespace BulksketchBridge.Square

open Aeneas Aeneas.Std

private theorem shiftRight32 (word : U64) :
    word >>> (32#i32) = Result.ok (⟨word.bv >>> (32 : Nat)⟩ : U64) := by rfl

private theorem canonical_mask (word : U64) :
    word &&& ~~~bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK = 0#u64 := by
  apply U64.bv_eq_imp_eq
  simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MASK,
    core.num.U64.MAX, U64.rMax]

private theorem square_to_reduce (input : U64) :
    bulksketch.field.gf64.square
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
      bulksketch.field.gf64.reduce
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        { lo := Spread.expectedWord input,
          hi := Spread.expectedWord (⟨input.bv >>> (32 : Nat)⟩ : U64) } := by
  simp only [bulksketch.field.gf64.square,
    bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField, lift, bind_ok,
    canonical_mask, ite_true, Spread.spread_refines, shiftRight32]

/-- Every actual square call with the real Gf64 dictionary returns the exact word.
The canonicality assertion, intermediate shifts and reduction all return normally. -/
theorem square_refines (input : U64) :
    bulksketch.field.gf64.square
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (expectedWord input) := by
  rw [square_to_reduce]
  obtain ⟨output, normal, exactBits, _⟩ := Gf64Reduce.reduce_refines
    { lo := Spread.expectedWord input,
      hi := Spread.expectedWord (⟨input.bv >>> (32 : Nat)⟩ : U64) }
  have outputEq : output = expectedWord input := by
    apply U64.bv_eq_imp_eq
    exact exactBits
  rw [normal, outputEq]

/-- The actual square's complete raw coefficient polynomial has the certified remainder. -/
theorem square_division_certificate (input : U64) :
    ∃ output : U64,
      bulksketch.field.gf64.square
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
      BulksketchProofs.Field.rawSquare128 input.bv =
        output.bv.setWidth 128 ^^^
          BulksketchProofs.Field.modulusMultiple128
            (BulksketchProofs.Field.spread64 (input.bv >>> 32) ^^^
              BulksketchProofs.Field.overflow64
                (BulksketchProofs.Field.spread64 (input.bv >>> 32))) := by
  refine ⟨expectedWord input, square_refines input, ?_⟩
  exact BulksketchProofs.Field.reduction_division_certificate
    (BulksketchProofs.Field.spread64 input.bv)
    (BulksketchProofs.Field.spread64 (input.bv >>> 32))

end BulksketchBridge.Square
