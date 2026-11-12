import BulksketchBridge.Algebra.TraceSpec

/-! The final Itoh–Tsujii exponent is a genuine field inverse. This generic
lemma uses a proved power-period equation, never a source-success premise. -/

namespace BulksketchBridge.Algebra.Gf64

/-- Every element satisfying the degree-64 binary-field power equation has
the expected inverse exponent. The zero case uses Mathlib's total inverse. -/
theorem inverse_power_of_period {K : Type*} [_root_.Field K] (value : K)
    (period : value ^ (2 ^ 64 : Nat) = value) :
    value ^ ((2 ^ 64 : Nat) - 2) = value⁻¹ := by
  by_cases zero : value = 0
  · subst value
    simp
  · apply (mul_left_cancel₀ zero)
    rw [mul_inv_cancel₀ zero]
    apply (mul_left_cancel₀ zero)
    rw [mul_one]
    calc
      value * (value * value ^ ((2 ^ 64 : Nat) - 2)) =
          value ^ (((2 ^ 64 : Nat) - 2) + 2) := by
            rw [pow_add, pow_two]
            ac_rfl
      _ = value ^ (2 ^ 64 : Nat) := by congr 1
      _ = value := period

/-- The actual irreducible polynomial quotient has the required power period. -/
theorem field_power_period (value : Field) :
    value ^ (2 ^ 64 : Nat) = value := by
  let : Fintype Field := Fintype.ofFinite Field
  have period := FiniteField.pow_card value
  simpa only [Fintype.card_eq_nat_card, field_natCard] using period

/-- The exact quotient's total inverse, including zero, is the chain exponent. -/
theorem field_inverse_power (value : Field) :
    value ^ ((2 ^ 64 : Nat) - 2) = value⁻¹ :=
  inverse_power_of_period value (field_power_period value)

/-- Specialization for all complete native words. -/
theorem word_inverse_power (input : BitVec 64) :
    toField input ^ ((2 ^ 64 : Nat) - 2) = (toField input)⁻¹ :=
  field_inverse_power (toField input)

end BulksketchBridge.Algebra.Gf64
