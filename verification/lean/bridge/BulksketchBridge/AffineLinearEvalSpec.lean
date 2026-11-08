import Arithmetic.AffineLinearEvalGenerated
import Arithmetic.Funs
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.AffineLinearEval

open Aeneas.Std BulksketchBridge.Algebra.Gf64
open bulksketch.backend.contract
open scoped BigOperators

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def CorrectArithmetic {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64) : Prop :=
  (∀ left right, kernels.ArithmeticInst.mul left right =
    bulksketch.field.gf64.mul fieldDictionary left right) ∧
  (∀ word, kernels.ArithmeticInst.square word = bulksketch.field.gf64.square fieldDictionary word)

/-- The coefficient at index i multiplies the `2^i` power of the input. -/
noncomputable def linearValueFrom (linear : Slice U64) (input : U64) (start : Nat) : Field :=
  ∑ offset ∈ Finset.range (linear.length - start),
    toField linear[start + offset]!.bv * toField input.bv ^ (2 ^ (start + offset))

def ActualLinearEvaluation : Prop :=
  ∀ {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (linear : Slice U64) (input : U64), CorrectArithmetic kernels →
    ∃ output : U64,
      bulksketch.decode.affine.linear_eval fieldDictionary kernels linear input = Result.ok output ∧
      toField output.bv = linearValueFrom linear input 0

end BulksketchBridge.AffineLinearEval
