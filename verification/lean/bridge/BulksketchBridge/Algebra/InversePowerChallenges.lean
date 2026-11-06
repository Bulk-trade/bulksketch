import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.Algebra.Gf64.InversePowerChallenges

/-- Exact field period, independent of an implementation power routine. -/
def fieldPowerPeriod : Prop :=
  ∀ value : Field, value ^ (2 ^ 64 : Nat) = value

/-- The exact exponent targeted by the original source inversion chain. -/
def fieldInverseExponent : Prop :=
  ∀ value : Field, value ^ ((2 ^ 64 : Nat) - 2) = value⁻¹

end BulksketchBridge.Algebra.Gf64.InversePowerChallenges
