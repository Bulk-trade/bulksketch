namespace BulksketchBridge.BmScalar

/-- The homogeneous BM buffer cursor relation. Each growth changes the
saved degree to the previous connection degree and resets shift to one. -/
structure Invariant (index budget degree previousLen shift : Nat) : Prop where
  degreeIndex : degree ≤ index
  degreeBudget : degree ≤ budget
  previousPositive : 1 ≤ previousLen
  previousBudget : previousLen ≤ budget + 1
  shiftPositive : 1 ≤ shift
  cursor : shift + degree + previousLen = index + 2

def candidateDegree (index degree : Nat) : Nat :=
  if 2 * degree ≤ index then index + 1 - degree else degree

def ShiftWindowBounds : Prop :=
  ∀ (index budget degree previousLen shift : Nat),
    Invariant index budget degree previousLen shift →
    let next := candidateDegree index degree
    next ≤ budget → degree ≤ next ∧ shift + previousLen ≤ next + 1 ∧ next + 1 ≤ budget + 1

end BulksketchBridge.BmScalar
