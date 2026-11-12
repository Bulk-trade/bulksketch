import BulksketchBridge.SyndromeUniquenessSpec

/-! A finite positive-moment recurrence for the ascending coefficients of the
monic reciprocal locator. The last available moment is `observed` and the
first available moment is one. -/

namespace BulksketchBridge.Reconciliation

open Polynomial Algebra.Gf64
open scoped BigOperators

noncomputable def supportLocator {K : Type*} [CommRing K]
    (roots : Finset K) : Polynomial K :=
  ∏ root ∈ roots, (X - C root)

noncomputable def positiveRecurrenceSum {K : Type*} [Semiring K]
    (roots : Finset K) (candidate : Polynomial K) (start : Nat) : K :=
  ∑ term ∈ Finset.range (candidate.natDegree + 1),
    candidate.coeff term * powerSum roots (start + term)

def positiveRecurrenceThrough {K : Type*} [Semiring K] (roots : Finset K)
    (candidate : Polynomial K) (observed : Nat) : Prop :=
  ∀ start, 0 < start → start + candidate.natDegree ≤ observed →
    positiveRecurrenceSum roots candidate start = 0

/-- A nonzero recurrence polynomial fitting enough positive moments contains
all support factors, and its degree is at least the support size. -/
def GF64PositiveLocatorMinimal : Prop :=
  ∀ (roots : Finset Field) (candidate : Polynomial Field) (observed : Nat),
    (0 : Field) ∉ roots → candidate ≠ 0 →
    roots.card + candidate.natDegree ≤ observed →
    positiveRecurrenceThrough roots candidate observed →
    supportLocator roots ∣ candidate ∧ roots.card ≤ candidate.natDegree

/-- A monic recurrence polynomial of at most support degree is exactly the
support locator. In particular this identifies every monic exact-degree fit. -/
def GF64PositiveLocatorUnique : Prop :=
  ∀ (roots : Finset Field) (candidate : Polynomial Field) (observed : Nat),
    (0 : Field) ∉ roots → candidate.Monic → candidate.natDegree ≤ roots.card →
    roots.card + candidate.natDegree ≤ observed →
    positiveRecurrenceThrough roots candidate observed →
    candidate = supportLocator roots

end BulksketchBridge.Reconciliation
