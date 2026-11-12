import Arithmetic.DenseExactDivideGenerated
import BulksketchBridge.RebuiltLfsrSpec

namespace BulksketchBridge.DenseExactDivide

open Aeneas.Std DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial

/-- The original exact-division wrapper keeps the returned remainder and raw
frames on both paths. Nonzero remainder clears exactly the quotient prefix. -/
def ActualExactDivide : Prop :=
  ∀ (division : DenseDivisionRuntime.DivRem) {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (a b q rem qOut remOut : Slice U64)
    (raw rawOut : Slice bulksketch.types.RawProduct) (qLen remLen : Usize),
    division field kernels a b q rem raw = .ok ((qLen, remLen), qOut, remOut, rawOut) →
    (remLen ≠ 0#usize → a.length < qOut.length) →
    exact_divide_into division field kernels a b q rem raw =
      if remLen = 0#usize then .ok (some qLen, qOut, remOut, rawOut)
      else .ok (none, restorePrefix qOut (zeroWords (prefixSlice qOut (a.length + 1))), remOut, rawOut)

end BulksketchBridge.DenseExactDivide
