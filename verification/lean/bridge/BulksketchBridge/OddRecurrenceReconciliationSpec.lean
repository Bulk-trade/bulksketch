import BulksketchBridge.OddRecurrenceSpec
import BulksketchBridge.ReconciliationLfsrSpec

namespace BulksketchBridge.Reconciliation

open Aeneas.Std Algebra.Gf64
open bulksketch.backend.contract

/-- Once the caller has matched the seed and built the squared locator, the
original scalar continuation decides exact equality of the complete odd row. -/
def GF64ScalarContinuationIffDirect : Prop :=
  ∀ {Backend : Type} (kernels : BulkKernels Backend bulksketch.field.Gf64)
    (roots : Finset Field) (odd squaredLocator : Slice U64),
    OddRecurrence.CorrectArithmetic kernels →
    (0 : Field) ∉ roots →
    squaredLocator.length = roots.card + 1 →
    (∀ lag, 1 ≤ lag → lag ≤ roots.card →
      toField squaredLocator[lag]!.bv = ((rebuiltLocator roots).coeff lag) ^ 2) →
    (∀ index, index < min roots.card odd.length →
      toField odd[index]!.bv = oddSyndrome roots index) →
    ∃ result : Bool,
      BulkKernels.odd_recurrence_matches.default kernels odd squaredLocator = Result.ok result ∧
      (result = true ↔ ∀ index, index < odd.length →
        toField odd[index]!.bv = oddSyndrome roots index)

end BulksketchBridge.Reconciliation
