import BulksketchBridge.CandidateNoOverhit
import BulksketchBridge.CandidateDeflateHandoff

namespace BulksketchBridge.CandidateOuter

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient
open Deflation RootRun
open bulksketch.decode.row bulksketch.decode.stages bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- For a fresh scan of distinct hints, the original candidate stage
    succeeds and delivers both native deflation invariants. -/
def ActualNativeCandidateSuccessHandoff : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64),
    HornerLaw kernels →
    ∀ (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
      (workspace : RowWorkspace) (meter : WorkMeter),
    WorkspaceAdmission.Admitted (workspaceLengths workspace) input.difference.length self.budget.nonzero.val →
    self.budget.nonzero.val ≤ input.difference.length → self.degree.val ≤ self.budget.nonzero.val →
    self.roots.pending = 0#usize → self.hits.val = 0 → input.candidates.val.Nodup →
    let locator := slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))
    locator.Monic → locator.natDegree = self.degree.val → locator.Splits → locator.roots.Nodup →
    (∀ point, locator.IsRoot point → point ≠ 0) →
    let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
    charge.1 = .Ok () →
    ∃ count roots values,
      let next := completedExecution self count false
      let written := candidateWorkspace input workspace roots values
      Execution.candidates RootSetup.gf64Dictionary kernels self input workspace meter =
        .ok (.Ok (.Ok (some .Deflation)), next, written, id, charge.2) ∧
      DeflateCandidateHandoff next input written ∧ DeflateCandidateMeaning next input written

theorem native_candidate_success_handoff : ActualNativeCandidateSuccessHandoff := by
  intro K kernels horner self input workspace meter admitted cap degreeBudget pending fresh unique
    locator monic degree split simple nonzero charge paid
  have bm : 4 * (input.difference.length + 1) ≤ workspace.bm.length := admitted.2.2.2.2.2.2.2.2.1
  have rootsRoom : self.budget.nonzero.val ≤ workspace.roots.length := admitted.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bounds : CandidateEntryBounds self input workspace :=
    ⟨degreeBudget.trans cap, by omega, degreeBudget.trans rootsRoom, by omega⟩
  obtain ⟨count, roots, values, reject, accepted, exactRun, _, distinct, countExact, rootList, rootPrefix, members⟩ :=
    native_candidate_distinct kernels horner self input workspace meter bounds unique paid
  obtain ⟨completeCount, _, _, success, _, completeBound⟩ :=
    native_candidate_no_overhit kernels horner self input workspace meter bounds fresh unique monic
      degree.le paid
  have same := Result.ok_injective (exactRun.symm.trans success)
  have acceptedRun : reject = false := by
    cases rejected : reject
    · rfl
    · have contradiction := congrArg Prod.fst same
      rw [rejected] at contradiction
      cases contradiction
  rw [acceptedRun] at same exactRun
  have exactHits : count = completeCount := congrArg (fun result => result.2.1.hits) same
  have countBound : count.val ≤ self.degree.val := exactHits ▸ completeBound
  have fits : count.val ≤ workspace.roots.length := countBound.trans (degreeBudget.trans rootsRoom)
  have hitLength : count.val = accepted.length := by omega
  have rootWidth : roots.length = workspace.roots.length := by
    change roots.val.length = workspace.roots.val.length
    rw [rootList, fresh, List.take_zero, List.nil_append, List.length_append, List.length_drop, ← hitLength]
    have fit : count.val ≤ workspace.roots.val.length := fits
    omega
  refine ⟨count, roots, values, exactRun, ?_⟩
  exact candidate_support_deflate_handoff self input workspace count roots values accepted admitted cap
    degreeBudget pending countBound rootWidth hitLength (rootPrefix fresh) distinct members monic degree split simple nonzero

#print axioms native_candidate_success_handoff

end BulksketchBridge.CandidateOuter
