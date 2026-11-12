import BulksketchBridge.BmScalarSpec

namespace BulksketchBridge.BmScalar

theorem initial (budget : Nat) : Invariant 0 budget 0 1 1 := by
  exact ⟨Nat.le_refl _, Nat.zero_le _, Nat.le_refl _, by omega, Nat.le_refl _, rfl⟩

theorem advance (index budget degree previousLen shift : Nat)
    (inv : Invariant index budget degree previousLen shift) :
    Invariant (index + 1) budget degree previousLen (shift + 1) := by
  obtain ⟨degreeIndex, degreeBudget, positive, previousBudget, shiftPositive, cursor⟩ := inv
  exact ⟨by omega, degreeBudget, positive, previousBudget, by omega, by omega⟩

theorem grow (index budget degree previousLen shift : Nat)
    (inv : Invariant index budget degree previousLen shift)
    (admitted : index + 1 - degree ≤ budget) :
    Invariant (index + 1) budget (index + 1 - degree) (degree + 1) 1 := by
  obtain ⟨degreeIndex, degreeBudget, _, _, _, _⟩ := inv
  exact ⟨by omega, admitted, by omega, by omega, by omega, by omega⟩

/-- On a growth step the shifted interval reaches exactly next degree plus
one. On a non-growth step it lies inside the existing degree plus one. -/
theorem shifted_window_bounds : ShiftWindowBounds := by
  intro index budget degree previousLen shift inv
  obtain ⟨degreeIndex, _, _, _, _, cursor⟩ := inv
  unfold candidateDegree
  split <;> intro bounded <;> omega

/-- The source's checked scalar operations are representable in an admitted
active iteration. The last syndrome index is below the input length. -/
theorem active_bounds (index budget degree previousLen shift capacity length max : Nat)
    (inv : Invariant index budget degree previousLen shift)
    (budgetBound : budget ≤ capacity) (active : index < 2 * capacity)
    (inputRoom : 2 * capacity + 1 ≤ length) (representable : length ≤ max) :
    degree ≤ index + 1 ∧ index + 1 < length ∧
      2 * degree ≤ max ∧ shift + 1 ≤ max ∧ capacity + 1 ≤ max := by
  obtain ⟨degreeIndex, degreeBudget, previousPositive, _, _, cursor⟩ := inv
  omega

end BulksketchBridge.BmScalar
