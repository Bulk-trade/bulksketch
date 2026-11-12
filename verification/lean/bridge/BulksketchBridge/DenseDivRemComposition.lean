import BulksketchBridge.DenseDivRem
import BulksketchBridge.RootDivideNative

namespace BulksketchBridge.DenseDivRem

open Aeneas Aeneas.Std BulksketchBridge DenseDivision
open bulksketch.backend.contract
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

def ActualNativeDivRem : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels → DenseMul.reduceAgrees kernels →
    BmTerminal.NativeInverse kernels →
    ∀ (a b q rem : Slice U64) (raw : Slice BmDiscrepancy.Raw),
      0 < b.length → b[b.length - 1]! ≠ 0#u64 →
      a.length + 1 ≤ q.length → a.length + 1 ≤ rem.length → a.length + 1 ≤ raw.length →
      div_rem_into DenseGcd.dictionary kernels a b q rem raw =
        .ok (expectedDivRem a b q rem raw (divisorInverse b[b.length - 1]!))

theorem actual_native_div_rem : ActualNativeDivRem :=
  fun kernels mul raw reduce inverse => direct_div_rem_refines kernels mul raw reduce inverse

/-- The exact original body discharges both previously explicit Euclidean GCD
division premises under the same native arithmetic laws. -/
theorem original_gcd_laws {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : MulWordLaw kernels) (raw : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (reduce : DenseMul.reduceAgrees kernels) (inverse : BmTerminal.NativeInverse kernels) :
    DenseGcd.DivisionLaw (fun {_ _} => div_rem_into) kernels ∧
      DenseGcd.DivisionMeaning (fun {_ _} => div_rem_into) kernels :=
  ⟨model_gcd_law div_rem_into kernels (direct_div_rem_refines kernels mul raw reduce inverse),
    model_gcd_meaning div_rem_into kernels (direct_div_rem_refines kernels mul raw reduce inverse)⟩

open RootDivide in
/-- Original root factor division with its original Dense div/rem call. -/
def ActualRootDivideWithDivRem : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels → DenseMul.reduceAgrees kernels →
    BmTerminal.NativeInverse kernels →
    ∀ (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
      (meter : WorkMeter),
      NativeDivideReady roots buffers →
      (∀ length start stop,
        (nativeCall roots buffers).1 = some length →
        Usize.checked_mul roots.pending roots.stride = some start →
        Usize.checked_add start length = some stop →
        CommitReady roots buffers factors stack (nativeCall roots buffers).2.1 length start stop) →
      Roots.divide (exact_divide_into div_rem_into) DenseGcd.dictionary kernels roots buffers factors stack meter =
        expected exactDivisionModel DenseGcd.dictionary kernels roots buffers factors stack meter

theorem original_root_divide_refines : ActualRootDivideWithDivRem := by
  intro K kernels mul raw reduce inverse roots buffers factors stack meter ready commit
  exact RootDivide.native_divide_refines div_rem_into kernels roots buffers factors stack meter
    (direct_div_rem_refines kernels mul raw reduce inverse) ready commit

end BulksketchBridge.DenseDivRem
