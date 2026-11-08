import BulksketchBridge.NewtonGuardSpec
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std Algebra.Gf64

noncomputable abbrev value (word : U64) : Field := toField word.bv

/-- The guard's cubic prefix is the monic coefficient list scaled by its
clearing denominator, with an unused zero word in the fifth slot. -/
def CubicClearedWordsMeaning : Prop :=
  ∀ (odd : Slice U64) (linear constant : Field),
    let s := value odd[0]!
    let p3 := value odd[1]!
    let p5 := value odd[2]!
    p3 = s ^ 3 + s * linear + constant →
    p5 = s ^ 5 + linear * p3 + constant * s ^ 2 →
    let denominator := p3 + s ^ 3
    let words := clearedWords odd 3
    words.1.val.map value = [constant * denominator, linear * denominator, s * denominator, denominator, 0] ∧
      value words.2 = denominator

/-- The quartic prefix is the five monic coefficients in ascending order,
scaled by the determinant of the source Newton system. -/
def QuarticClearedWordsMeaning : Prop :=
  ∀ (odd : Slice U64) (quadratic linear constant : Field),
    let s := value odd[0]!
    let p3 := value odd[1]!
    let p5 := value odd[2]!
    let p7 := value odd[3]!
    p3 = s ^ 3 + s * quadratic + linear →
    p5 = s ^ 5 + quadratic * p3 + linear * s ^ 2 + constant * s →
    p7 = s * p3 ^ 2 + quadratic * p5 + linear * s ^ 4 + constant * p3 →
    let denominator := (p3 + s ^ 3) * p3 + s * (p5 + s ^ 5)
    let words := clearedWords odd 4
    words.1.val.map value =
      [constant * denominator, linear * denominator, quadratic * denominator, s * denominator, denominator] ∧
      value words.2 = denominator

def CubicDenominatorMeaning : Prop :=
  ∀ (odd : Slice U64) (r0 r1 r2 : Field),
    value odd[0]! = r0 + r1 + r2 →
    value odd[1]! = r0 ^ 3 + r1 ^ 3 + r2 ^ 3 →
    value (clearedWords odd 3).2 = (r0 + r1) * (r0 + r2) * (r1 + r2)

def QuarticDenominatorMeaning : Prop :=
  ∀ (odd : Slice U64) (r0 r1 r2 r3 : Field),
    value odd[0]! = r0 + r1 + r2 + r3 →
    value odd[1]! = r0 ^ 3 + r1 ^ 3 + r2 ^ 3 + r3 ^ 3 →
    value odd[2]! = r0 ^ 5 + r1 ^ 5 + r2 ^ 5 + r3 ^ 5 →
    value (clearedWords odd 4).2 =
      (r0 + r1) * (r0 + r2) * (r0 + r3) * (r1 + r2) * (r1 + r3) * (r2 + r3)

end BulksketchBridge.NewtonGuard
