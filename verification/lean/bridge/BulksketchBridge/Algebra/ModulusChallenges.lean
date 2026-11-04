import BulksketchBridge.Algebra.ModulusSpec

/-! Independent exact-polynomial challenge, frozen before proof search. -/

namespace BulksketchBridge.Algebra.ModulusChallenges

open Polynomial

/-- Irreducibility of the complete polynomial over the two-element field. -/
def exactPolynomialIrreducible : Prop :=
  Irreducible (X ^ 64 + X ^ 4 + X ^ 3 + X + 1 : Polynomial (ZMod 2))

end BulksketchBridge.Algebra.ModulusChallenges
