import Arithmetic.CubicGenerated
import Arithmetic.InverseUsingGenerated
import BulksketchBridge.CubeRootSpec
import BulksketchBridge.MapsQuadraticSpec

namespace BulksketchBridge.Cubic

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def CorrectArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  CubeRoot.CorrectArithmetic kernels ∧
  (∀ a, kernels.ArithmeticInst.inverse a = bulksketch.field.maps.inverse fieldDictionary a) ∧
  (∀ a, kernels.ArithmeticInst.solve_quadratic a =
    bulksketch.field.maps.solve_quadratic fieldDictionary a)

def ActualQuadraticHelperReturnsExactOption : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    (∀ word, kernels.ArithmeticInst.square word = bulksketch.field.gf64.square fieldDictionary word) →
    (∀ word, kernels.ArithmeticInst.solve_quadratic word =
      bulksketch.field.maps.solve_quadratic fieldDictionary word) →
    ∀ target, bulksketch.decode.deg34.quadratic fieldDictionary kernels target =
      Result.ok (MapsQuadratic.expectedSolution target)

/-- Every word returned by the original speculative cubic helper is a root
of the supplied monic cubic over GF64. -/
def ActualCubicReturnsOnlyRoots : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (a b c : U64),
    CorrectArithmetic kernels → ∃ output : Option (Array U64 3#usize),
      bulksketch.decode.deg34.cubic fieldDictionary kernels a b c = Result.ok output ∧
      ∀ (roots : Array U64 3#usize), output = some roots → ∀ (root : U64), root ∈ roots.val →
        toField root.bv ^ 3 + toField a.bv * toField root.bv ^ 2 +
          toField b.bv * toField root.bv + toField c.bv = 0

end BulksketchBridge.Cubic
