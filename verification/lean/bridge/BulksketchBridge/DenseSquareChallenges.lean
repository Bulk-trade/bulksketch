import Arithmetic.DenseSquareGenerated
import Arithmetic.Funs
import BulksketchBridge.DenseNormalizationSpec
import BulksketchBridge.SquareSpec

namespace BulksketchBridge.DenseSquareChallenges

open Aeneas.Std
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

def coefficient (a dst : Slice U64) (i : Nat) : U64 :=
  if i < 2 * a.length then
    if i % 2 = 0 then Square.expectedWord a[i / 2]! else 0#u64
  else dst[i]!

/-- Exact frame, canonical length, and checked error order for the original body. -/
def actualSquareIntoReturnsExactFrame : Prop :=
  ∀ (K : Type) (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    (∀ input, kernels.ArithmeticInst.square input =
      bulksketch.field.gf64.square bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input) →
    ∀ (a dst : Slice U64) (raw : Slice bulksketch.types.RawProduct),
      if 2 * a.length ≤ Usize.max then
        if 2 * a.length ≤ dst.length ∧ 2 * a.length ≤ raw.length then
          ∃ (length : Usize) (output : Slice U64),
            square_into bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels a dst raw =
              Result.ok (length, output, raw) ∧
            output.length = dst.length ∧
            (∀ i, i < dst.length → output[i]! = coefficient a dst i) ∧
            length.val = DenseNormalization.normalizedLength (output.val.take (2 * a.length))
        else
          square_into bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels a dst raw =
            Result.fail Error.assertionFailure
      else
        square_into bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels a dst raw =
          Result.fail Error.integerOverflow

end BulksketchBridge.DenseSquareChallenges
