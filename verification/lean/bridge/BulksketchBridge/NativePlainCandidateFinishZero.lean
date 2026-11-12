import BulksketchBridge.NativePlainCandidateFinish
import BulksketchBridge.PortableZeroBudgetFinish

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 RootRun RootWorkBudget Reconciliation RebuiltLfsr
open ExecutionFinish
open bulksketch.backend.portable bulksketch.decode.row bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)

def ActualNativePlainCandidateFinishZero : Prop :=
  ∀ (support : Finset Field) (input : RowInput) (before initial : RootDrainState Portable) (steps : Nat),
      let capacity := input.difference.length
      let budget := before.execution.budget.nonzero.val
      let beta := before.execution.budget.total
      0 < capacity → capacity ≤ 65535 → budget = 0 → beta.val ≤ 65535 →
      support.card ≤ budget →
      (∀ i < capacity, toField input.difference[i]!.bv = oddSyndrome support i) →
      input.candidates.val = [] → PlainCandidate before input support →
      before.meter.used.val + plainCandidateWork capacity support.card beta ≤ before.meter.limit.val →
      SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary portableKernels input
        steps initial before id →
      ∃ (sorted : Slice U64) (written : RowWorkspace) (paid : WorkMeter),
        let reply := if support.card = 0 ∧ beta = before.execution.budget.nonzero then RowResult.Equal
          else RowResult.Decoded sorted
        finish nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary portableKernels initial.execution
          input initial.workspace initial.meter = .ok (.Ok reply, written, id, paid) ∧
        rootSupport sorted = support ∧ sorted.val.Nodup ∧ sorted.length = support.card ∧
        sorted.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧
        written.roots.val.take support.card = sorted.val ∧ paid.limit = before.meter.limit ∧ paid.exhausted = false ∧
        paid.used.val ≤ before.meter.used.val + plainCandidateWork capacity support.card beta

theorem native_plain_candidate_finish_zero : ActualNativePlainCandidateFinishZero := by
  intro support input before initial steps capacity budget beta positive capacityFits budgetZero betaFits
    supportFits odd noHints ready reserve prior
  have empty : support.card = 0 := Nat.eq_zero_of_le_zero (budgetZero ▸ supportFits)
  obtain rfl : support = ∅ := Finset.card_eq_zero.mp empty
  have degreeZero : before.execution.degree.val = 0 := ready.degree.trans (Finset.card_empty)
  have locator := ready.locator
  simp only [supportLocator, Finset.prod_empty] at locator
  have oddZero : ∀ i < input.difference.length, toField input.difference[i]!.bv = 0 := by
    simpa only [oddSyndrome, powerSum, Finset.sum_empty] using odd
  have costZero : plainCandidateWork capacity 0 beta = verificationReserve capacity 0 beta := by
    simp [plainCandidateWork, rootsEnvelope, chain]
  rw [Finset.card_empty, costZero] at reserve ⊢
  simpa only [eq_self, true_and] using PortableDecoder.zero_budget_finish input before initial steps
    ready.state ready.noProbe ready.pending ready.hits budgetZero degreeZero locator ready.workspace
    positive capacityFits betaFits oddZero noHints ready.live reserve prior

#print axioms native_plain_candidate_finish_zero

end BulksketchBridge.ExecutionDriver
