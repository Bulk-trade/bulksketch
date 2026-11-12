import BulksketchBridge.NewtonGuardMomentSpec
import BulksketchBridge.ReconciliationLocatorSpec

namespace BulksketchBridge.NewtonGuard

open Aeneas.Std Algebra.Gf64 Reconciliation
open bulksketch.backend.contract
open NewtonGuardResidual (CorrectArithmetic)

/-- A cleared locator matching the support satisfies every residual the
original wrapper selects. The denominator and cleared-word correspondence
are explicit premises, separate from the original boolean and frame proof. -/
def ActualGuardAcceptsSupport : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Finset Field) (odd scratch : Slice U64) (degree : Usize),
    CorrectArithmetic kernels → Admitted odd degree scratch →
    roots.card = degree.val → OddMoments roots odd →
    let words := clearedWords odd degree.val
    let updated := clearedFrame scratch words
    words.2 ≠ 0#u64 →
    (∀ index < degree.val,
      value updated[index]! = value words.2 * (supportLocator roots).coeff index) →
    bulksketch.decode.deg34.guard fieldDictionary kernels odd degree scratch =
      .ok (true, updated)

end BulksketchBridge.NewtonGuard
