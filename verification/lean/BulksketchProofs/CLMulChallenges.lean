import BulksketchProofs.Field.CLMulSpec

namespace BulksketchProofs.CLMulChallenges

def completeCoefficientConvolution : Prop :=
  ∀ (left right : BitVec 64) (index : Nat), index < 128 →
    (Field.clmul128 left right).getLsbD index = Field.clmulCoefficient left right index

def noCoefficientBeyondDegree126 : Prop :=
  ∀ (left right : BitVec 64), (Field.clmul128 left right).getLsbD 127 = false

def polynomialHasDegreeAtMost126 : Prop :=
  ∀ (left right : BitVec 64) (index : Nat), 127 ≤ index →
    Field.clmulCoefficient left right index = false

end BulksketchProofs.CLMulChallenges
