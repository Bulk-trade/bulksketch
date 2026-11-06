import Arithmetic.Funs
import BulksketchBridge.Algebra.WordSpec

/-! Exact generated-body contracts in Mathlib's independently constructed field.
Normal returns are conclusions for all native-width inputs. -/

namespace BulksketchBridge.Algebra.Gf64.WordNativeChallenges

open Aeneas.Std

def actualReductionIsQuotientRemainder : Prop :=
  ∀ product : bulksketch.types.RawProduct, ∃ output : U64,
    bulksketch.field.gf64.reduce
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField product = Result.ok output ∧
    toField output.bv = AdjoinRoot.mk modulus
      (wordPolynomial (BulksketchProofs.Field.join128 product.lo.bv product.hi.bv))

def actualMultiplicationIsFieldMultiplication : Prop :=
  ∀ left right : U64, ∃ output : U64,
    bulksketch.field.gf64.mul
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right = Result.ok output ∧
    toField output.bv = toField left.bv * toField right.bv

def actualSquareIsFieldSquare : Prop :=
  ∀ input : U64, ∃ output : U64,
    bulksketch.field.gf64.square
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    toField output.bv = toField input.bv ^ 2

def actualFrobeniusIsFieldPower : Prop :=
  ∀ (input : U64) (power : U32), ∃ output : U64,
    bulksketch.field.gf64.frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input power = Result.ok output ∧
    toField output.bv = toField input.bv ^ (2 ^ power.val)

end BulksketchBridge.Algebra.Gf64.WordNativeChallenges
