import BulksketchProofs.Field.SpreadSpec

/-! Fixed universal contracts for the next arithmetic milestone. -/

namespace BulksketchProofs.Challenges

def spreadPreservesExactlyTheEvenCoefficients : Prop :=
  ∀ (word : BitVec 64) (index : Nat), index < 64 →
    (Field.spread64 word).getLsbD index =
      if index % 2 = 0 then word.getLsbD (index / 2) else false

def rawSquareDoublesExactlyTheCoefficientIndices : Prop :=
  ∀ (word : BitVec 64) (index : Nat), index < 128 →
    (Field.rawSquare128 word).getLsbD index =
      if index % 2 = 0 then word.getLsbD (index / 2) else false

end BulksketchProofs.Challenges
