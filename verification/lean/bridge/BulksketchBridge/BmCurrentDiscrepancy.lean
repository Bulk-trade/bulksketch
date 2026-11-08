import BulksketchBridge.BmEvenStep
import BulksketchBridge.BmSyndromePolynomials

namespace BulksketchBridge.BmCurrentDiscrepancy

open Aeneas.Std BmEvenStep BmDiscrepancy BmSyndromePolynomials Algebra.Gf64
open bulksketch.backend.contract

/-- The discrepancy used by the original active-step transition is
the current coefficient of the characteristic-two polynomial residual. -/
theorem current_discrepancy {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (raw : RawArithmetic kernels) (reduce : ReduceArithmetic kernels)
    (connection syndromes : Slice U64) (degree index : Usize)
    (bounded : PreludeBounds connection syndromes degree index) (degreeBound : degree.val ≤ index.val) :
    (BmParity.residual (connectionPolynomial connection degree.val)
      (syndromePolynomial syndromes)).coeff (index.val + 1) =
      toField (deltaWord connection syndromes degree index).bv := by
  obtain ⟨first, last, prelude⟩ := prelude_refines kernels raw reduce connection syndromes degree index bounded
  obtain ⟨delta, fold, _, dot⟩ := source_dot_refines kernels raw reduce connection syndromes degree.val index.val
    bounded.connection bounded.lower bounded.syndromes
  rw [prelude.paidLoop] at fold
  change Aeneas.Std.bind (.ok ((rawDelta connection syndromes degree index).lo,
    (rawDelta connection syndromes degree index).hi)) (fun words =>
      kernels.ArithmeticInst.reduce ⟨words.1, words.2⟩) = .ok delta at fold
  rw [bind_ok] at fold
  change kernels.ArithmeticInst.reduce (rawDelta connection syndromes degree index) = .ok delta at fold
  rw [prelude.reduced] at fold
  have same := Result.ok_injective fold
  have degreeActual := connection_degree connection degree.val
  rw [BmParity.current_discrepancy _ _ _ (by omega), discrepancy_polynomial connection syndromes
      degree.val (index.val + 1) (by omega) bounded.syndromes, ← dot, same]

end BulksketchBridge.BmCurrentDiscrepancy
