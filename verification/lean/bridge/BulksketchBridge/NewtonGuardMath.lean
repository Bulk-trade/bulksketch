import BulksketchBridge.NewtonGuardMathSpec
import BulksketchBridge.NewtonClearing
import BulksketchBridge.Algebra.WordSquare
import Mathlib.Algebra.CharP.Algebra

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std Algebra.Gf64

set_option maxRecDepth 2048

private theorem value_mul (a b : U64) : value (mulWord a b) = value a * value b := toField_mul _ _
private theorem value_square (a : U64) : value (squareWord a) = value a ^ 2 := toField_square _
private theorem value_xor (a b : U64) : value (a ^^^ b) = value a + value b := toField_xor _ _
private theorem value_zero : value 0#u64 = 0 := toField_zero

private theorem mul_square (s : Field) : s * s ^ 2 = s ^ 3 := by ring

private theorem square_square (s : Field) : (s ^ 2) ^ 2 = s ^ 4 := by rw [← pow_mul]

private theorem mul_fourth (s : Field) : s * s ^ 4 = s ^ 5 := by ring

theorem cubic_cleared_words : CubicClearedWordsMeaning := by
  intro odd linear constant
  dsimp only
  intro third fifth
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  obtain ⟨constantEq, linearEq⟩ := NewtonClearing.cubic _ linear constant _ _ third fifth
  simp only [clearedWords, eq_self, ite_true, Array.make, Array.from_val,
    List.map_cons, List.map_nil, value_mul, value_xor, value_square, mul_square, value_zero]
  rw [constantEq, linearEq]
  exact ⟨rfl, trivial⟩

theorem quartic_cleared_words : QuarticClearedWordsMeaning := by
  intro odd quadratic linear constant
  dsimp only
  intro third fifth seventh
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  obtain ⟨constantEq, linearEq, quadraticEq⟩ :=
    NewtonClearing.quartic _ quadratic linear constant _ _ _ third fifth seventh
  simp only [clearedWords, show (4 : Nat) ≠ 3 by decide, ite_false, Array.make, Array.from_val,
    List.map_cons, List.map_nil, value_mul, value_xor, value_square, mul_square, square_square, mul_fourth]
  rw [constantEq, linearEq, quadraticEq]
  exact ⟨rfl, trivial⟩

theorem cubic_denominator : CubicDenominatorMeaning := by
  intro odd r0 r1 r2 first third
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  simp only [clearedWords, eq_self, ite_true, value_mul, value_xor, value_square, mul_square,
    first, third]
  exact NewtonClearing.cubic_denominator r0 r1 r2

theorem quartic_denominator : QuarticDenominatorMeaning := by
  intro odd r0 r1 r2 r3 first third fifth
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  simp only [clearedWords, show (4 : Nat) ≠ 3 by decide, ite_false, Prod.snd,
    value_mul, value_xor, value_square, mul_square, square_square, mul_fourth, first, third, fifth]
  exact NewtonClearing.quartic_denominator r0 r1 r2 r3

end BulksketchBridge.NewtonGuard
