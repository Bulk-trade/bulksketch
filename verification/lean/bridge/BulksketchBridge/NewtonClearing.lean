import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.Ring

namespace BulksketchBridge.NewtonClearing

variable {K : Type} [Field K] [CharP K 2]

local macro "ring_two" : tactic =>
  `(tactic| ring_nf <;> simp [CharTwo.two_eq_zero, CharTwo.ofNat_eq_mod])

/-- The cubic guard's low numerator words equal the constant and linear
coefficients multiplied by the source denominator. -/
theorem cubic (s u v p3 p5 : K)
    (third : p3 = s ^ 3 + s * u + v)
    (fifth : p5 = s ^ 5 + u * p3 + v * s ^ 2) :
    let a := p3 + s ^ 3
    let b := p5 + p3 * s ^ 2
    (a ^ 2 + s * b = v * a) ∧ b = u * a := by
  let a := p3 + s ^ 3
  let b := p5 + p3 * s ^ 2
  have aEq : a = s * u + v := by
    simp only [a, third]
    ring_two
  have bEq : b = u * a := by
    simp only [b, aEq, fifth, third]
    ring_two
  change a ^ 2 + s * b = v * a ∧ b = u * a
  refine ⟨?_, bEq⟩
  rw [bEq, aEq]
  ring_two

/-- The quartic guard clears the two-by-two Newton system. Its three low
words equal the constant, linear and quadratic coefficients times the
determinant, in exactly the source order. -/
theorem quartic (s u v w p3 p5 p7 : K)
    (third : p3 = s ^ 3 + s * u + v)
    (fifth : p5 = s ^ 5 + u * p3 + v * s ^ 2 + w * s)
    (seventh : p7 = s * p3 ^ 2 + u * p5 + v * s ^ 4 + w * p3) :
    let a := p3 + s ^ 3
    let b := p5 + p3 * s ^ 2
    let d := p5 + s ^ 5
    let c := p7 + s * p3 ^ 2 + a * s ^ 4
    let denominator := a * p3 + s * d
    let u2 := b * p3 + s * c
    a * c + b * d = w * denominator ∧
      a * denominator + s * u2 = v * denominator ∧ u2 = u * denominator := by
  let a := p3 + s ^ 3
  let b := p5 + p3 * s ^ 2
  let d := p5 + s ^ 5
  let c := p7 + s * p3 ^ 2 + a * s ^ 4
  let denominator := a * p3 + s * d
  let u2 := b * p3 + s * c
  have aEq : a = s * u + v := by
    simp only [a, third]
    ring_two
  have bEq : b = a * u + s * w := by
    simp only [b, aEq, fifth, third]
    ring_two
  have cEq : c = d * u + w * p3 := by
    simp only [c, d, aEq, seventh]
    ring_two
  have uEq : u2 = u * denominator := by
    simp only [u2, denominator, bEq, cEq]
    ring_two
  change a * c + b * d = w * denominator ∧ a * denominator + s * u2 = v * denominator ∧ u2 = u * denominator
  refine ⟨?_, ?_, uEq⟩
  · simp only [bEq, cEq, denominator]
    ring_two
  · rw [uEq, aEq]
    ring_two

theorem cubic_third_moment (r0 r1 r2 : K) :
    let s := r0 + r1 + r2
    let u := r0 * r1 + r0 * r2 + r1 * r2
    let v := r0 * r1 * r2
    r0 ^ 3 + r1 ^ 3 + r2 ^ 3 = s ^ 3 + s * u + v := by
  dsimp only
  ring_two

theorem quartic_third_moment (r0 r1 r2 r3 : K) :
    let s := r0 + r1 + r2 + r3
    let u := r0 * r1 + r0 * r2 + r0 * r3 + r1 * r2 + r1 * r3 + r2 * r3
    let v := r0 * r1 * r2 + r0 * r1 * r3 + r0 * r2 * r3 + r1 * r2 * r3
    r0 ^ 3 + r1 ^ 3 + r2 ^ 3 + r3 ^ 3 = s ^ 3 + s * u + v := by
  dsimp only
  ring_two

/-- The source cubic denominator is the Vandermonde product. -/
theorem cubic_denominator (r0 r1 r2 : K) :
    let s := r0 + r1 + r2
    let p3 := r0 ^ 3 + r1 ^ 3 + r2 ^ 3
    p3 + s ^ 3 = (r0 + r1) * (r0 + r2) * (r1 + r2) := by
  dsimp only
  ring_two

/-- The source quartic determinant is the six-pair Vandermonde product. -/
theorem quartic_denominator (r0 r1 r2 r3 : K) :
    let s := r0 + r1 + r2 + r3
    let p3 := r0 ^ 3 + r1 ^ 3 + r2 ^ 3 + r3 ^ 3
    let p5 := r0 ^ 5 + r1 ^ 5 + r2 ^ 5 + r3 ^ 5
    let a := p3 + s ^ 3
    let d := p5 + s ^ 5
    a * p3 + s * d =
      (r0 + r1) * (r0 + r2) * (r0 + r3) * (r1 + r2) * (r1 + r3) * (r2 + r3) := by
  dsimp only
  ring_two


end BulksketchBridge.NewtonClearing