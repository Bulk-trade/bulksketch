import BulksketchBridge.CubicSpec
import BulksketchBridge.Algebra.WordSquare
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Two

namespace BulksketchBridge.Cubic

open Aeneas.Std Algebra.Gf64 bulksketch.decode.deg34

private theorem omega_squared : toField OMEGA.bv ^ 2 = toField OMEGA.bv + 1 := by
  have bits : BulksketchProofs.Field.Period.squareWord OMEGA.bv = OMEGA.bv ^^^ 1 := by
    unfold OMEGA
    decide +kernel
  simpa only [toField_square, toField_xor, toField_one] using congrArg toField bits

private theorem cube_sum {K : Type*} [_root_.Field K] [CharP K 2] (u v : K) :
    (u + v) ^ 3 + (u * v) * (u + v) = u ^ 3 + v ^ 3 := by
  calc
    _ = u ^ 3 + v ^ 3 + 2 * (2 * (u ^ 2 * v + u * v ^ 2)) := by ring
    _ = _ := by rw [show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, add_zero]

private theorem shift_cubic {K : Type*} [_root_.Field K] [CharP K 2] (a b c y : K) :
    (a + y) ^ 3 + a * (a + y) ^ 2 + b * (a + y) + c =
      y ^ 3 + (a ^ 2 + b) * y + (a * b + c) := by
  calc
    _ = y ^ 3 + (a ^ 2 + b) * y + (a * b + c) +
        2 * (a ^ 3 + 2 * a ^ 2 * y + 2 * a * y ^ 2) := by ring
    _ = _ := by rw [show (2 : K) = 0 from CharTwo.two_eq_zero, zero_mul, add_zero]

private theorem translated_root {K : Type*} [_root_.Field K] [CharP K 2] (a b c u v : K)
    (product : u * v = a ^ 2 + b) (sum : u ^ 3 + v ^ 3 = a * b + c) :
    (a + u + v) ^ 3 + a * (a + u + v) ^ 2 + b * (a + u + v) + c = 0 := by
  rw [add_assoc a u v, shift_cubic, ← product, cube_sum, sum, CharTwo.add_self_eq_zero]

noncomputable def evaluate (a b c value : Field) : Field := value ^ 3 + a * value ^ 2 + b * value + c

/-- All three of the source's characteristic-two Cardano expressions solve
 the monic cubic. The literal omega relation is checked in the word model. -/
theorem cardano_roots (a b c u v : Field)
    (product : u * v = a ^ 2 + b) (sum : u ^ 3 + v ^ 3 = a * b + c) :
    let omega := toField OMEGA.bv
    evaluate a b c (a + u + v) = 0 ∧
    evaluate a b c (a + omega * u + omega * v + v) = 0 ∧
    evaluate a b c (a + omega * u + u + omega * v) = 0 := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  let omega := toField OMEGA.bv
  change evaluate a b c (a + u + v) = 0 ∧
    evaluate a b c (a + omega * u + omega * v + v) = 0 ∧
    evaluate a b c (a + omega * u + u + omega * v) = 0
  have square : omega ^ 2 = omega + 1 := omega_squared
  have cube : omega ^ 3 = 1 := by
    rw [pow_succ omega 2, square, add_mul, one_mul, ← pow_two, square,
      add_right_comm, CharTwo.add_self_eq_zero, zero_add]
  have productOmega : omega * omega ^ 2 = 1 := by rw [← pow_succ', cube]
  have sixth : (omega ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show (2 : Nat) * 3 = 3 * 2 by decide, pow_mul, cube, one_pow]
  have rotatedProduct : (omega * u) * (omega ^ 2 * v) = a ^ 2 + b := by
    calc
      _ = (omega * omega ^ 2) * (u * v) := by ring
      _ = _ := by rw [productOmega, one_mul, product]
  have rotatedSum : (omega * u) ^ 3 + (omega ^ 2 * v) ^ 3 = a * b + c := by
    rw [mul_pow, mul_pow, cube, sixth, one_mul, one_mul, sum]
  have otherProduct : (omega ^ 2 * u) * (omega * v) = a ^ 2 + b := by
    calc
      _ = (omega * omega ^ 2) * (u * v) := by ring
      _ = _ := by rw [productOmega, one_mul, product]
  have otherSum : (omega ^ 2 * u) ^ 3 + (omega * v) ^ 3 = a * b + c := by
    rw [mul_pow, mul_pow, cube, sixth, one_mul, one_mul, sum]
  refine ⟨translated_root a b c u v product sum, ?_, ?_⟩
  · rw [show a + omega * u + omega * v + v = a + omega * u + omega ^ 2 * v by rw [square]; ring]
    exact translated_root a b c _ _ rotatedProduct rotatedSum
  · rw [show a + omega * u + u + omega * v = a + omega ^ 2 * u + omega * v by rw [square]; ring]
    exact translated_root a b c _ _ otherProduct otherSum

/-- A quadratic auxiliary solution gives the radicand identity even when the
source substitutes q for a zero intermediate. -/
theorem radicand_law (p q z : Field) (nonzero : q ≠ 0)
    (quadratic : z ^ 2 + z = p ^ 3 * q⁻¹ ^ 2) :
    let t := q * z
    let w := if t = 0 then q else t
    w ^ 2 + q * w = p ^ 3 := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have inverseSquare : q ^ 2 * q⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ nonzero, one_pow]
  have original : (q * z) ^ 2 + q * (q * z) = p ^ 3 := by
    calc
      _ = q ^ 2 * (z ^ 2 + z) := by ring
      _ = p ^ 3 * (q ^ 2 * q⁻¹ ^ 2) := by rw [quadratic]; ring
      _ = _ := by rw [inverseSquare, mul_one]
  dsimp only
  by_cases zero : q * z = 0
  · rw [zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at original
    rw [ite_eq_left zero, pow_two, CharTwo.add_self_eq_zero, original]
  · rwa [ite_eq_right zero]

/-- The selected cube root and its companion have the exact depressed cubic
product and sum of cubes. -/
theorem companion_law (p q w u : Field) (nonzero : u ≠ 0)
    (root : u ^ 3 = w) (radicand : w ^ 2 + q * w = p ^ 3) :
    u * (p * u⁻¹) = p ∧ u ^ 3 + (p * u⁻¹) ^ 3 = q := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  have product : u * (p * u⁻¹) = p := by
    rw [mul_left_comm, mul_inv_cancel₀ nonzero, mul_one]
  refine ⟨product, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero 3 nonzero)
  calc
    u ^ 3 * (u ^ 3 + (p * u⁻¹) ^ 3) = (u ^ 3) ^ 2 + (u * (p * u⁻¹)) ^ 3 := by
      simp only [mul_add, pow_two, mul_pow]
    _ = w ^ 2 + (w ^ 2 + q * w) := by rw [root, product, ← radicand]
    _ = u ^ 3 * q := by rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add, ← root, mul_comm]

end BulksketchBridge.Cubic
