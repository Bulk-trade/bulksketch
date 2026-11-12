import Arithmetic.TimesXModGenerated
import BulksketchBridge.DenseCoefficientPolynomial
import BulksketchBridge.SlicePolynomial

namespace BulksketchBridge.TimesXMod

open Aeneas.Std DenseCoefficient SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract

def shiftedWords (words : Slice U64) : Slice U64 :=
  (words.setSlice! 1 (words.val.take (words.length - 1))).setAtNat 0 0#u64

def ExactScaleXor {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ (dst src : Slice U64) (scale : U64), dst.length = src.length →
    ∃ output,
      kernels.ArithmeticInst.scale_xor dst src scale = Result.ok output ∧
      output.length = dst.length ∧
      ∀ i < dst.length,
        output[i]! = dst[i]! ^^^ (⟨multiplyWord scale.bv src[i]!.bv⟩ : U64)

/-- Exact original overlapping shift, zero write and scale-XOR call.
The admitted nonempty destination fits within the source modulus prefix. -/
def ActualTimesXMod : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (coefficients modulus : Slice U64),
    0 < coefficients.length → coefficients.length ≤ modulus.length →
    bulksketch.poly.dense.times_x_mod field kernels coefficients modulus =
      kernels.ArithmeticInst.scale_xor (shiftedWords coefficients)
        (prefixSlice modulus coefficients.length) coefficients[coefficients.length - 1]!

/-- The actual native shift represents multiplication by X modulo the
admitted monic modulus and returns a residue of the same width. -/
def TimesXModPolynomial : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    ExactScaleXor kernels → ∀ (coefficients modulus : Slice U64),
    0 < coefficients.length → modulus.length = coefficients.length + 1 →
    modulus[coefficients.length]! = 1#u64 →
    ∃ output,
      bulksketch.poly.dense.times_x_mod bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        kernels coefficients modulus = .ok output ∧ output.length = coefficients.length ∧
      slicePolynomial modulus ∣ X * slicePolynomial coefficients + slicePolynomial output

end BulksketchBridge.TimesXMod
