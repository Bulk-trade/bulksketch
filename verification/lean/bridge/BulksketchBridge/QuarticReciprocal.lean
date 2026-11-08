import BulksketchBridge.AffineQuarticAlgebra
import BulksketchBridge.Algebra.InversePower

namespace BulksketchBridge.QuarticReciprocal

variable {K : Type} [Field K] [CharP K 2]

def evaluate (a b c d z : K) : K := z ^ 4 + a * z ^ 3 + b * z ^ 2 + c * z + d

def denominator (b d shift : K) : K := shift ^ 4 + b * shift ^ 2 + d

def reciprocal (a b d shift z : K) : K :=
  z ^ 4 + ((b + a * shift) * (denominator b d shift)⁻¹) * z ^ 2 +
    (a * (denominator b d shift)⁻¹) * z + (denominator b d shift)⁻¹

private theorem sum_cubed (x y : K) :
    (x + y) ^ 3 = x ^ 3 + y ^ 3 + x ^ 2 * y + x * y ^ 2 := by
  calc
    _ = x ^ 3 + y ^ 3 + x ^ 2 * y + x * y ^ 2 +
      2 * (x ^ 2 * y + x * y ^ 2) := by ring
    _ = _ := by rw [show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, add_zero]

private theorem sum_fourth (x y : K) : (x + y) ^ 4 = x ^ 4 + y ^ 4 := by
  simp only [show (4 : Nat) = 2 * 2 by decide, pow_mul, CharTwo.add_sq]

theorem translated (a b c d shift z : K) (shiftEq : a * shift ^ 2 = c) :
    evaluate a b c d (z + shift) =
      z ^ 4 + a * z ^ 3 + (b + a * shift) * z ^ 2 + denominator b d shift := by
  unfold evaluate denominator
  rw [sum_fourth, sum_cubed, CharTwo.add_sq]
  calc
    _ = z ^ 4 + a * z ^ 3 + (b + a * shift) * z ^ 2 +
        (shift ^ 4 + b * shift ^ 2 + d) + (a * shift ^ 2 + c) * (z + shift) := by ring
    _ = _ := by rw [shiftEq, CharTwo.add_self_eq_zero, zero_mul, add_zero]

/-- A nonzero root of the normalized affine reciprocal maps back to a root
of the original general quartic by the source reciprocal and shift. -/
theorem reciprocal_root_iff (a b c d shift z : K)
    (shiftEq : a * shift ^ 2 = c) (nonzeroD : denominator b d shift ≠ 0) (nonzeroZ : z ≠ 0) :
    reciprocal a b d shift z = 0 ↔ evaluate a b c d (z⁻¹ + shift) = 0 := by
  have identity : denominator b d shift * reciprocal a b d shift z =
      z ^ 4 * evaluate a b c d (z⁻¹ + shift) := by
    rw [translated a b c d shift z⁻¹ shiftEq]
    unfold reciprocal
    field_simp
    ring
  constructor
  · intro root
    rw [root, mul_zero] at identity
    exact (mul_eq_zero.mp identity.symm).resolve_left (pow_ne_zero _ nonzeroZ)
  · intro root
    rw [root, mul_zero] at identity
    exact (mul_eq_zero.mp identity).resolve_left nonzeroD

theorem denominator_is_shift_value (a b c d shift : K) (shiftEq : a * shift ^ 2 = c) :
    denominator b d shift = evaluate a b c d shift := by
  simpa using (translated a b c d shift 0 shiftEq).symm

omit [CharP K 2] in
theorem reverse_step (prefixProduct root shift : K) (prefixNZ : prefixProduct ≠ 0) (rootNZ : root ≠ 0) :
    prefixProduct * (prefixProduct * root)⁻¹ + shift = root⁻¹ + shift ∧
      (prefixProduct * root)⁻¹ * root = prefixProduct⁻¹ := by
  constructor <;> field_simp

open BulksketchBridge.Algebra.Gf64 in
theorem shift_squares_to_ratio (ratio : BulksketchBridge.Algebra.Gf64.Field) :
    (((ratio ^ (2 ^ 31 : Nat)) ^ (2 ^ 31 : Nat)) ^ 2) ^ 2 = ratio := by
  rw [← pow_mul, ← pow_mul, ← pow_mul]
  exact field_power_period ratio


theorem reciprocal_nonzero (a b d shift z : K)
    (nonzeroD : denominator b d shift ≠ 0) (root : reciprocal a b d shift z = 0) :
    z ≠ 0 := by
  intro zero
  subst z
  have inverseNZ := inv_ne_zero nonzeroD
  apply inverseNZ
  simpa [reciprocal] using root

theorem reciprocal_solvable_iff (a b c d shift : K)
    (shiftEq : a * shift ^ 2 = c) (nonzeroD : denominator b d shift ≠ 0) :
    (∃ z, reciprocal a b d shift z = 0) ↔ ∃ z, evaluate a b c d z = 0 := by
  constructor
  · rintro ⟨z, root⟩
    exact ⟨z⁻¹ + shift, (reciprocal_root_iff a b c d shift z shiftEq nonzeroD
      (reciprocal_nonzero a b d shift z nonzeroD root)).mp root⟩
  · rintro ⟨x, root⟩
    have outside : x + shift ≠ 0 := by
      intro same
      have xShift : x = shift := by
        calc
          x = (x + shift) + shift := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
          _ = shift := by rw [same, zero_add]
      apply nonzeroD
      rw [denominator_is_shift_value a b c d shift shiftEq, ← xShift, root]
    refine ⟨(x + shift)⁻¹, (reciprocal_root_iff a b c d shift _ shiftEq nonzeroD (inv_ne_zero outside)).mpr ?_⟩
    rw [inv_inv, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    exact root

end BulksketchBridge.QuarticReciprocal
