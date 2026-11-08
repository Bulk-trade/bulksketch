import Arithmetic.DirectTwoGenerated
import Arithmetic.InverseUsingGenerated
import BulksketchBridge.InverseFieldSpec
import BulksketchBridge.MapsQuadraticSpec
import BulksketchBridge.SquareSpec

namespace BulksketchBridge.DirectTwo

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract bulksketch.decode.direct

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def CorrectArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  (∀ a b, kernels.ArithmeticInst.mul a b = bulksketch.field.gf64.mul fieldDictionary a b) ∧
  (∀ a, kernels.ArithmeticInst.square a = bulksketch.field.gf64.square fieldDictionary a) ∧
  (∀ a, kernels.ArithmeticInst.inverse a = bulksketch.field.maps.inverse fieldDictionary a) ∧
  (∀ a, kernels.ArithmeticInst.solve_quadratic a = bulksketch.field.maps.solve_quadratic fieldDictionary a)

noncomputable def inverseWord (sum : U64) : U64 := ⟨wordFieldEquiv.symm (toField sum.bv)⁻¹⟩

noncomputable def productWord (sum third : U64) : U64 :=
  Inverse.multiplyNativeWord (third ^^^ Inverse.multiplyNativeWord (Square.expectedWord sum) sum)
    (inverseWord sum)

noncomputable def targetWord (sum third : U64) : U64 :=
  Inverse.multiplyNativeWord (productWord sum third) (Square.expectedWord (inverseWord sum))

noncomputable def expectedPair (sum third : U64) : Option Pair := do
  if productWord sum third = 0#u64 then none else
    let normalized ← MapsQuadratic.expectedSolution (targetWord sum third)
    let first := Inverse.multiplyNativeWord sum normalized
    let second := first ^^^ sum
    if first = second ∨ first = 0#u64 ∨ second = 0#u64 then none else
      some { roots := Array.make 2#usize [first, second] }

def ActualDirectTwoReturnsNormalizedPair : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (sum third : U64),
    CorrectArithmetic kernels → sum ≠ 0#u64 →
    two fieldDictionary kernels sum third = Result.ok (expectedPair sum third)

/-- A successful speculative pair has the two supplied odd syndromes.
Further odd words are checked by the row verifier. -/
def ActualDirectTwoSound : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (sum third : U64) (pair : Pair),
    CorrectArithmetic kernels → sum ≠ 0#u64 →
    two fieldDictionary kernels sum third = Result.ok (some pair) →
    ∃ first second : U64,
      pair.roots = Array.make 2#usize [first, second] ∧ first ≠ second ∧
      first ≠ 0#u64 ∧ second ≠ 0#u64 ∧
      toField first.bv + toField second.bv = toField sum.bv ∧
      toField first.bv ^ 3 + toField second.bv ^ 3 = toField third.bv

end BulksketchBridge.DirectTwo
