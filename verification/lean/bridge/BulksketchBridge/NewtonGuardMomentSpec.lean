import BulksketchBridge.NewtonGuardMathSpec
import BulksketchBridge.SyndromeUniquenessSpec

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std Algebra.Gf64 Reconciliation NewtonGuardResidual
open scoped BigOperators

def OddMoments (roots : Finset Field) (odd : Slice U64) : Prop :=
  ∀ index < odd.length, value odd[index]! = oddSyndrome roots index

noncomputable def momentResidual (roots : Finset Field) (cleared : Slice U64)
    (denominator : U64) (degree index : Nat) : Field :=
  value denominator * powerSum roots (2 * index + 1) +
    ∑ offset ∈ Finset.range degree,
      value cleared[degree - (offset + 1)]! * powerSum roots (2 * index + 1 - (offset + 1))

/-- The source scans only the two selected odd moments. The exact word
predicate agrees with the cleared recurrence over the quotient field. -/
def ResidualMomentMeaning : Prop :=
  ∀ (roots : Finset Field) (odd cleared : Slice U64) (denominator : U64) (degree : Nat),
    (degree = 3 ∨ degree = 4) → OddMoments roots odd →
    (residualOK odd cleared denominator degree = true ↔
      ∀ index, degree ≤ index → index < min odd.length (degree + 2) →
        momentResidual roots cleared denominator degree index = 0)

end BulksketchBridge.NewtonGuard
