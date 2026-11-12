import Arithmetic.SliceKernelGenerated
import Arithmetic.Funs
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.SliceKernelChallenges

open Aeneas.Std BulksketchBridge.Algebra.Gf64
open bulksketch.backend.contract

/-- Coefficient of the fixed-length product with `1 + root * X`. -/
def coefficientAfter (original : Slice U64) (root : U64) (index : Nat) : U64 :=
  if index = 0 then original[index]!
  else original[index]! ^^^ ⟨multiplyWord original[index - 1]!.bv root.bv⟩

/-- Normal completion and the entire mutable slice frame, for every length.
The production trait method receives its multiplication implementation from the
caller. The contract identifies that method with the actual GF64 body. -/
def actualMultiplyLinearReturnsExactFrame : Prop :=
  ∀ (Backend : Type) (kernels : BulkKernels Backend bulksketch.field.Gf64),
    (∀ left right, kernels.ArithmeticInst.mul left right =
      bulksketch.field.gf64.mul bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right) →
    ∀ (coefficients : Slice U64) (root : U64), ∃ output : Slice U64,
      BulkKernels.multiply_linear.default kernels coefficients root = Result.ok output ∧
      output.length = coefficients.length ∧
      ∀ index : Nat, index < coefficients.length →
        output[index]! = coefficientAfter coefficients root index

/-- The default fallback returns false with both caller buffers intact. -/
def actualSquareModFallbackPreservesBuffers : Prop :=
  ∀ (Backend Field : Type) (a table dst : Slice U64)
    (raw : Slice bulksketch.types.RawProduct),
    BulkKernels.square_mod.default Backend Field a table dst raw = Result.ok (false, dst, raw)

end BulksketchBridge.SliceKernelChallenges
