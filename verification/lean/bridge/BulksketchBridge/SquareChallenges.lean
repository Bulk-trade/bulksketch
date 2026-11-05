import Arithmetic.Funs
import BulksketchBridge.SquareSpec

/-! Universal actual-source square propositions, frozen before proof search. -/

namespace BulksketchBridge.SquareChallenges

open Aeneas Aeneas.Std

/-- The real extracted Gf64 instance gives exact normal output for every word. -/
def normalResultMatchesModel : Prop :=
  ∀ input : U64,
    bulksketch.field.gf64.square
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input =
        Result.ok (Square.expectedWord input)

/-- The actual square output is the canonical-degree polynomial-square remainder. -/
def rawSquareDivisionCertificate : Prop :=
  ∀ input : U64, ∃ output : U64,
    bulksketch.field.gf64.square
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField input = Result.ok output ∧
    BulksketchProofs.Field.rawSquare128 input.bv =
      output.bv.setWidth 128 ^^^
        BulksketchProofs.Field.modulusMultiple128
          (BulksketchProofs.Field.spread64 (input.bv >>> 32) ^^^
            BulksketchProofs.Field.overflow64
              (BulksketchProofs.Field.spread64 (input.bv >>> 32)))

end BulksketchBridge.SquareChallenges
