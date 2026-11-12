import Arithmetic.NormalizeGenerated
import Arithmetic.InverseUsingGenerated
import BulksketchBridge.DirectTwoSpec

namespace BulksketchBridge.Normalize

open Aeneas.Std Algebra.Gf64 bulksketch.backend.contract

abbrev fieldDictionary := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
abbrev mulWord := Inverse.multiplyNativeWord

/-- The two arithmetic methods invoked by normalization. -/
def CorrectArithmetic {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  (∀ left right, kernels.ArithmeticInst.mul left right = bulksketch.field.gf64.mul fieldDictionary left right) ∧
  (∀ word, kernels.ArithmeticInst.inverse word = bulksketch.field.maps.inverse fieldDictionary word)

/-- Ascending normalized coefficients and the caller's untouched tail. -/
noncomputable def expectedCoefficient (cleared : Slice U64) (s : U64) (degree : Nat)
    (factor : Slice U64) (index : Nat) : U64 :=
  if index < degree - 1 then mulWord cleared[index]! (DirectTwo.inverseWord cleared[5]!)
  else if index = degree - 1 then s
  else if index = degree then 1#u64
  else factor[index]!

noncomputable def expectedOutput (cleared : Slice U64) (s : U64) (degree : Nat)
    (factor : Slice U64) : Slice U64 :=
  Slice.from (List.ofFn fun index : Fin factor.length => expectedCoefficient cleared s degree factor index.val)
    (by simp)

/-- The original degree-three and degree-four wrapper returns the complete
normalized scratch slice after passing the nonsingular Newton guard. -/
def ActualNormalizeReturnsExactFrame : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), CorrectArithmetic kernels →
    ∀ (cleared : Slice U64) (s : U64) (degree : Usize) (factor : Slice U64),
      (degree.val = 3 ∨ degree.val = 4) → 6 ≤ cleared.length → degree.val < factor.length →
      cleared[5]! ≠ 0#u64 →
      bulksketch.decode.deg34.normalize fieldDictionary kernels cleared s degree factor =
        Result.ok (expectedOutput cleared s degree.val factor)

/-- The exact ascending coefficient meaning transported into GF64. -/
def ActualNormalizeFieldCoefficients : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), CorrectArithmetic kernels →
    ∀ (cleared : Slice U64) (s : U64) (degree : Usize) (factor : Slice U64),
      (degree.val = 3 ∨ degree.val = 4) → 6 ≤ cleared.length → degree.val < factor.length →
      cleared[5]! ≠ 0#u64 →
      ∃ output : Slice U64,
        bulksketch.decode.deg34.normalize fieldDictionary kernels cleared s degree factor = Result.ok output ∧
        output.length = factor.length ∧ ∀ index, index < factor.length →
          toField output[index]!.bv =
            if index < degree.val - 1 then toField cleared[index]!.bv * (toField cleared[5]!.bv)⁻¹
            else if index = degree.val - 1 then toField s.bv
            else if index = degree.val then 1
            else toField factor[index]!.bv

end BulksketchBridge.Normalize
