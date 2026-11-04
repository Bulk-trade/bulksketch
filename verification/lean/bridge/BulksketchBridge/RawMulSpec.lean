import Arithmetic.Funs
import BulksketchProofs.Field.CLMulSpec

/-! Frozen complete-word contracts for original raw multiplication and composition
with reduction. Every operand pair is quantified; success and all output bits are
conclusions. The real extracted Gf64 dictionary is named directly. -/

namespace BulksketchBridge.RawMul

open Aeneas.Std

def expectedProduct (left right : U64) : bulksketch.types.RawProduct :=
  { lo := ⟨(BulksketchProofs.Field.clmul128 left.bv right.bv).setWidth 64⟩
    hi := ⟨((BulksketchProofs.Field.clmul128 left.bv right.bv) >>> 64).setWidth 64⟩ }

def ReturnsCompleteProduct : Prop :=
  ∀ (left right : U64),
    bulksketch.field.gf64.raw_mul
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right =
        Result.ok (expectedProduct left right)

def ReturnsCoefficientConvolution : Prop :=
  ∀ (left right : U64) (index : Nat), index < 128 →
    ∃ product : bulksketch.types.RawProduct,
      bulksketch.field.gf64.raw_mul
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right = Result.ok product ∧
      (BulksketchProofs.Field.join128 product.lo.bv product.hi.bv).getLsbD index =
        BulksketchProofs.Field.clmulCoefficient left.bv right.bv index

def ReducedMultiplication : Prop :=
  ∀ (left right : U64), ∃ output : U64,
    bulksketch.field.gf64.mul
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right = Result.ok output ∧
    BulksketchProofs.Field.clmul128 left.bv right.bv =
      output.bv.setWidth 128 ^^^
        BulksketchProofs.Field.modulusMultiple128
          ((expectedProduct left right).hi.bv ^^^
            BulksketchProofs.Field.overflow64 (expectedProduct left right).hi.bv)

end BulksketchBridge.RawMul
