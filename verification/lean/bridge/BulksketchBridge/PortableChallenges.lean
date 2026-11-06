import Arithmetic.PortableGenerated
import BulksketchBridge.Algebra.TraceSpec
import BulksketchBridge.RawMulSpec
import BulksketchBridge.SquareSpec
import BulksketchProofs.Field.MapsSpec

/-! Fixed full-input contracts for the seven original Portable forwarding bodies.
The actual Gf64 dictionary is named directly. Every source normal return is a
conclusion; no contract assumes an enclosing source call succeeds. -/
namespace BulksketchBridge.PortableChallenges

open Aeneas.Std BulksketchBridge.Algebra.Gf64

/-- Exact normal native multiplication and its ordinary quotient-field meaning. -/
def actualMultiplicationIsFieldMultiplication : Prop :=
  ∀ left right : U64,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right =
        Result.ok (⟨multiplyWord left.bv right.bv⟩ : U64) ∧
    toField (multiplyWord left.bv right.bv) = toField left.bv * toField right.bv

def actualSquareIsFieldSquare : Prop :=
  ∀ input : U64,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.square
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (BulksketchBridge.Square.expectedWord input) ∧
    toField (BulksketchBridge.Square.expectedWord input).bv = toField input.bv ^ 2

def actualFrobeniusIsFullFieldPower : Prop :=
  ∀ (input : U64) (power : U32),
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.frobenius
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input power =
        Result.ok (⟨BulksketchProofs.Field.Period.iterateSquare power.val input.bv⟩ : U64) ∧
    toField (BulksketchProofs.Field.Period.iterateSquare power.val input.bv) =
      toField input.bv ^ (2 ^ power.val)

/-- The complete source output byte, with its upper seven bits constrained. -/
def actualTraceIsAlgebraTrace : Prop :=
  ∀ input : U64, ∃ output : U8,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.trace
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    output.val ≤ 1 ∧
    Algebra.trace (ZMod 2) Field (toField input.bv) = (output.val : ZMod 2)

/-- The chosen quadratic root has a zero free coefficient and is unique among
all such represented field roots; trace-one inputs return no root. -/
def actualQuadraticHasNormalizedFieldMeaning : Prop :=
  ∀ input : U64, ∃ output : Option U64,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.solve_quadratic
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    match output with
    | none => Algebra.trace (ZMod 2) Field (toField input.bv) = 1
    | some solution =>
      toField solution.bv ^ 2 + toField solution.bv = toField input.bv ∧
      solution.bv.getLsbD 0 = false ∧
      ∀ other : BitVec 64,
        toField other ^ 2 + toField other = toField input.bv →
        other.getLsbD 0 = false → other = solution.bv

/-- Every bit of the full unreduced product is retained in the source result. -/
def actualRawMultiplicationReturnsFullProduct : Prop :=
  ∀ left right : U64,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.raw_mul
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField left right =
        Result.ok (BulksketchBridge.RawMul.expectedProduct left right)

/-- Every complete 128-bit input returns its canonical quotient representative. -/
def actualReductionIsExactQuotientRemainder : Prop :=
  ∀ product : bulksketch.types.RawProduct, ∃ output : U64,
    bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.reduce
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField product = Result.ok output ∧
    output.bv = BulksketchProofs.Field.reduceFold64 product.lo.bv product.hi.bv ∧
    toField output.bv = AdjoinRoot.mk modulus
      (wordPolynomial (BulksketchProofs.Field.join128 product.lo.bv product.hi.bv))

end BulksketchBridge.PortableChallenges
