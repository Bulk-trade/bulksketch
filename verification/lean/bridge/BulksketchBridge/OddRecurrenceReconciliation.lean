import BulksketchBridge.OddRecurrenceReconciliationSpec
import BulksketchBridge.OddRecurrence
import BulksketchBridge.ReconciliationLfsr

namespace BulksketchBridge.Reconciliation

open Aeneas.Std Algebra.Gf64
open scoped BigOperators

theorem gf64_scalar_continuation_iff_direct : GF64ScalarContinuationIffDirect := by
  intro Backend kernels roots odd squaredLocator arithmetic nonzero length coefficients seed
  obtain ⟨result, normal, accepted⟩ := OddRecurrence.default_refines kernels odd squaredLocator
    arithmetic (by omega)
  have degree : squaredLocator.length - 1 = roots.card := by omega
  have sums (index : Nat) :
      OddRecurrence.lagSum odd squaredLocator index 1 roots.card =
        oddContinuation (rebuiltLocator roots) roots.card (fun i => toField odd[i]!.bv) index := by
    unfold OddRecurrence.lagSum oddContinuation
    apply Finset.sum_congr rfl
    intro offset inRange
    have bounded := Finset.mem_range.mp inRange
    have coefficient := coefficients (offset + 1) (by omega) (by omega)
    simp only [OddRecurrence.lagTerm, Nat.add_comm 1 offset, coefficient]
    exact mul_comm _ _
  refine ⟨result, normal, ?_⟩
  rw [accepted]
  have recurrence := gf64_rebuilt_verification_iff_direct roots
    (fun i => toField odd[i]!.bv) odd.length nonzero
  simp only [OddRecurrence.continuationMatches, degree, sums]
  exact ⟨fun tail => recurrence.mp ⟨seed, tail⟩, fun allWords => (recurrence.mpr allWords).2⟩

end BulksketchBridge.Reconciliation
