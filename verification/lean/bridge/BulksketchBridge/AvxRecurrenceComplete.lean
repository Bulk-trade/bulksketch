import BulksketchBridge.AvxRecurrenceLoop
import BulksketchBridge.AvxRecurrenceLag

namespace BulksketchBridge.AvxRecurrence

open Aeneas.Std Aeneas.Std.AvxSquareRuntime
open bulksketch.backend.x86_vpclmul512

theorem original_inner_block (loadModel : Load) (loadLaw : AvxSquare.LoadLaw loadModel) :
    InnerBlockLaw loadModel := by
  intro odd squared index len degree atLeast endRoom short degreeRoom
  exact lag_block_sum loadModel loadLaw odd squared index len degree atLeast degreeRoom endRoom short

/-- The original checked AVX entry agrees with the scalar recurrence under
the supplied masked-load contract. The inner lag, reduction, and masked
outer comparison are all checked original generated bodies. -/
def ActualNativeAvxRecurrence : Prop :=
  ∀ (loadModel : Load), AvxSquare.LoadLaw loadModel →
    ∀ (odd squared : Slice U64), 0 < squared.length →
      ∃ answer : Bool, odd_recurrence_matches loadModel odd squared = .ok answer ∧
        (answer = true ↔ OddRecurrence.continuationMatches odd squared)

theorem native_avx_recurrence : ActualNativeAvxRecurrence := by
  intro loadModel loadLaw odd squared positive
  exact native_avx_recurrence_from_inner loadModel loadLaw (original_inner_block loadModel loadLaw)
    odd squared positive

#print axioms original_inner_block
#print axioms native_avx_recurrence

end BulksketchBridge.AvxRecurrence
