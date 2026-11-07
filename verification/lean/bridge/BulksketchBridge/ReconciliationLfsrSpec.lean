import BulksketchBridge.SyndromeUniquenessSpec

/-! The polynomial and recurrence rebuilt from a candidate support. The
continuation visits lags `1` through `degree`, using ascending coefficients. -/

namespace BulksketchBridge.Reconciliation

open Polynomial Algebra.Gf64
open scoped BigOperators

noncomputable def rebuiltLocator {K : Type*} [CommSemiring K]
    (roots : Finset K) : Polynomial K :=
  ∏ root ∈ roots, (1 + C root * X)

noncomputable def oddContinuation {K : Type*} [CommSemiring K]
    (locator : Polynomial K) (degree : Nat) (row : Nat → K) (index : Nat) : K :=
  ∑ offset ∈ Finset.range degree, (locator.coeff (offset + 1)) ^ 2 * row (index - (offset + 1))

/-- The true odd sequence satisfies the rebuilt squared-coefficient recurrence
at every continuation index. -/
def GF64RebuiltLocatorRecurrence : Prop :=
  ∀ (roots : Finset Field), (0 : Field) ∉ roots →
    ∀ index, roots.card ≤ index →
      oddSyndrome roots index = oddContinuation (rebuiltLocator roots) roots.card
        (oddSyndrome roots) index

/-- Checking the seed and the entire recurrence tail is exactly equivalent
to direct comparison of all odd syndromes within the row capacity. -/
def GF64RebuiltVerificationIffDirect : Prop :=
  ∀ (roots : Finset Field) (row : Nat → Field) (capacity : Nat), (0 : Field) ∉ roots →
    (((∀ index, index < min roots.card capacity → row index = oddSyndrome roots index) ∧
      (∀ index, roots.card ≤ index → index < capacity →
        row index = oddContinuation (rebuiltLocator roots) roots.card row index)) ↔
    (∀ index, index < capacity → row index = oddSyndrome roots index))

end BulksketchBridge.Reconciliation
