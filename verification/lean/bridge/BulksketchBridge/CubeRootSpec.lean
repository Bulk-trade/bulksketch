import Arithmetic.CubeRootGenerated
import Arithmetic.Funs
import BulksketchBridge.Algebra.WordSpec

namespace BulksketchBridge.CubeRoot

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

def CorrectArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  (∀ a b, kernels.ArithmeticInst.mul a b = bulksketch.field.gf64.mul fieldDictionary a b) ∧
  (∀ a, kernels.ArithmeticInst.square a = bulksketch.field.gf64.square fieldDictionary a) ∧
  (∀ a power, kernels.ArithmeticInst.frobenius a power =
    bulksketch.field.gf64.frobenius fieldDictionary a power)

def cubeExponent : Nat := (2 ^ 64 + 2) / 9

/-- The original helper returns a nonzero cube root exactly when one exists.
On success its complete word is determined by the fixed chain exponent. -/
def ActualCubeRootComplete : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) (input : U64),
    CorrectArithmetic kernels → ∃ output : Option U64,
      bulksketch.decode.deg34.cube_root fieldDictionary kernels input = Result.ok output ∧
      match output with
      | none => ¬∃ root : Field, root ≠ 0 ∧ root ^ 3 = toField input.bv
      | some root => toField root.bv ≠ 0 ∧ toField root.bv ^ 3 = toField input.bv ∧
          toField root.bv = toField input.bv ^ cubeExponent

end BulksketchBridge.CubeRoot
