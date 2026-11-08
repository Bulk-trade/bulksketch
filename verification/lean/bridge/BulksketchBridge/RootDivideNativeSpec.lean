import BulksketchBridge.RootDivideSpec
import BulksketchBridge.DenseDivisionComposition

namespace BulksketchBridge.RootDivide

open Aeneas.Std Aeneas.Std.RootDivideRuntime
open DenseCoefficient BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial (exact_divide_into)

/-- Scratch admission for the native Dense exact-division callee. -/
structure NativeDivideReady (roots : Roots) (buffers : FactorWork) : Prop extends DivideReady roots buffers where
  divisorPositive : 0 < roots.gcd_len.val
  divisorNonzero : (prefixSlice buffers.gcd roots.gcd_len.val)[roots.gcd_len.val - 1]! ≠ 0#u64
  quotientRoom : buffers.modulus.length + 1 ≤ roots.degree.val + 2
  remainderRoom : buffers.modulus.length + 1 ≤ buffers.work.length - (roots.degree.val + 2)
  rawRoom : buffers.modulus.length + 1 ≤ buffers.raw.length

/-- Independent result and scratch frame of exact division, from the checked
descending division model. The original exact wrapper clears the quotient on
nonzero remainder. -/
noncomputable def exactDivisionResult (a b q rem : Slice U64) (raw : Slice RawProduct) :
    Option Usize × Slice U64 × Slice U64 × Slice RawProduct :=
  let result := DenseDivision.expectedDivRem a b q rem raw (DenseDivision.divisorInverse b[b.length - 1]!)
  if result.1.2 = 0#usize then (some result.1.1, result.2.1, result.2.2.1, result.2.2.2)
  else (none, DenseDivision.cleared result.2.1 (a.length + 1), result.2.2.1, result.2.2.2)

noncomputable def exactDivisionModel : ExactDivide :=
  fun _ _ a b q rem raw => .ok (exactDivisionResult a b q rem raw)

noncomputable def nativeCall (roots : Roots) (buffers : FactorWork) :
    Option Usize × Slice U64 × Slice U64 × Slice RawProduct :=
  exactDivisionResult buffers.modulus (prefixSlice buffers.gcd roots.gcd_len.val)
    (prefixSlice buffers.work (roots.degree.val + 2))
    (tail buffers.work (roots.degree.val + 2)) buffers.raw

/-- Original factor division using the original Dense exact-division wrapper.
Only the underlying div/rem model law and caller scratch admission remain
explicit. The stage frame is independent of the native exact wrapper. -/
def ActualNativeRootDivide : Prop :=
  ∀ (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter : WorkMeter),
    DenseDivision.RefinesModel division kernels →
    NativeDivideReady roots buffers →
    (∀ length start stop,
      (nativeCall roots buffers).1 = some length →
      Usize.checked_mul roots.pending roots.stride = some start →
      Usize.checked_add start length = some stop →
      CommitReady roots buffers factors stack (nativeCall roots buffers).2.1 length start stop) →
    Roots.divide (exact_divide_into division) DenseGcd.dictionary kernels roots buffers factors stack meter =
      expected exactDivisionModel DenseGcd.dictionary kernels roots buffers factors stack meter

end BulksketchBridge.RootDivide
