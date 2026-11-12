import BulksketchBridge.FrobeniusConstSpec

namespace BulksketchBridge.FrobeniusConstChallenges

open Aeneas.Std

/-- Both original loops, all checked arithmetic and byte conversions return the
complete canonical square, for every native operand. -/
def actualConstSquareMatchesWord : Prop :=
  ∀ input : U64,
    bulksketch.field.frobenius.square input =
      Result.ok (⟨BulksketchProofs.Field.Period.squareWord input.bv⟩ : U64)

end BulksketchBridge.FrobeniusConstChallenges
