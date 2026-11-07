import BulksketchBridge.DenseSquareChallenges
import BulksketchBridge.DenseCoefficientPolynomial

namespace BulksketchBridge.DenseSquare

open Aeneas.Std BulksketchBridge.Algebra.Gf64
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open SliceKernels DenseCoefficient

def SquareIntoPolynomialRefines : Prop :=
  ∀ (Backend : Type) (kernels : bulksketch.backend.contract.BulkKernels Backend bulksketch.field.Gf64),
    (∀ input, kernels.ArithmeticInst.square input =
      bulksketch.field.gf64.square bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input) →
    ∀ (a dst : Slice U64) (raw : Slice bulksketch.types.RawProduct),
      2 * a.length ≤ Usize.max →
      2 * a.length ≤ dst.length →
      2 * a.length ≤ raw.length →
      ∃ (length : Usize) (output : Slice U64),
        square_into bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels a dst raw =
          Result.ok (length, output, raw) ∧
        slicePolynomial (prefixSlice output length.val) = slicePolynomial a ^ 2

end BulksketchBridge.DenseSquare
