import BulksketchBridge.NativeCandidateDeflateDriver
import BulksketchBridge.RootTraversalInvariant

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime Algebra.Gf64 Polynomial DenseCoefficient SliceKernels
open CandidateOuter Deflation
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next)

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

def ActualNativeTraversalAdmission : Prop :=
  ∀ (canonicalize : Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    AffineEnumerate.HornerLaw kernels → (∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b)) →
    ∀ (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace)
      (meter finalMeter : WorkMeter),
    self.state = .Running .CandidateEvaluation → self.degree_probe = none →
    WorkspaceAdmission.Admitted (RootRun.workspaceLengths workspace) input.difference.length self.budget.nonzero.val →
    0 < self.budget.nonzero.val → self.budget.nonzero.val ≤ input.difference.length →
    self.degree.val ≤ self.budget.nonzero.val →
    self.roots.pending = 0#usize → self.hits.val = 0 → input.candidates.val.Nodup →
    let original := slicePolynomial (prefixSlice workspace.bm (self.degree.val + 1))
    original.Monic → original.natDegree = self.degree.val → original.Splits → original.roots.Nodup →
    (∀ point, original.IsRoot point → point ≠ 0) →
    let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
    charge.1 = .Ok () →
    StageCharge.chargeResult charge.2 (deflateCost self.degree) = (.Ok (), finalMeter) →
    ∃ (count : Usize) (roots values : Slice U64) (final : FinalState),
      let candidate := completedExecution self count false
      let next := { candidate with state := .Running .Deflation }
      let scanned := candidateWorkspace input workspace roots values
      let updated := finishedRoots next.roots final.degree
      let stage := ClosedLeafAdvance.stageFor updated
      let residual := activeLocator final.locator final.degree
      let joined := joinedWorkspace (deflateFrame next scanned (input.difference.length + 1)) final.locator final.quotient
      let written := RootSetup.startedWorkspace final.degree joined
      let beforeState := { next with roots := updated }
      nativeCandidateDriver canonicalize kernels self input workspace meter =
        .ok (.Ok (progress .CandidateEvaluation candidate), next, scanned, id, charge.2) ∧
      nativeCandidateDriver canonicalize kernels next input scanned charge.2 =
        .ok (.Ok (progress .Deflation beforeState), { beforeState with state := .Running stage }, written, id, finalMeter) ∧
      RootRun.RootTraversalInvariant original updated written input.difference.length self.budget.nonzero.val

theorem native_traversal_admission : ActualNativeTraversalAdmission := by
  intro canonicalize K kernels horner mul self input workspace meter finalMeter state probe admitted
    positive cap degreeBudget pending fresh unique original monic degree split simple nonzero charge paid deflatePaid
  obtain ⟨count, roots, values, final, candidateRan, deflateRan, _, represented, balance, _, emptied,
    sized, layout, mass, active, residualMonic, residualDegree, residualSplit, residualSimple, residualNonzero, _⟩ :=
    native_candidate_deflate_driver canonicalize kernels horner mul self input workspace meter finalMeter state
      probe admitted positive cap degreeBudget pending fresh unique monic degree split simple nonzero paid deflatePaid
  refine ⟨count, roots, values, final, candidateRan, deflateRan, ?_⟩
  dsimp only at sized layout mass represented active emptied ⊢
  refine RootRun.traversal_invariant_at_start original _ _ _ _ _ sized layout emptied ?_
    (mass.trans degree.symm) (degree.trans_le degreeBudget) represented
    ⟨residualMonic, residualDegree, residualSplit, residualSimple, residualNonzero⟩ active
  change (ClosedLeafAdvance.usizeWord (final.degree.val + 1)).val = final.degree.val + 1
  let written := RootSetup.startedWorkspace final.degree
    (joinedWorkspace (deflateFrame
      { completedExecution self count false with state := .Running .Deflation }
      (candidateWorkspace input workspace roots values) (input.difference.length + 1))
      final.locator final.quotient)
  have room : 8 * (self.budget.nonzero.val + 1) ≤ written.polynomials.length := sized.polynomials
  have wordBound : written.polynomials.length ≤ Usize.max := written.polynomials.length_ineq
  have fit : final.degree.val + 1 ≤ Usize.max := by omega
  exact ClosedLeafAdvance.word_val _ fit

#print axioms native_traversal_admission

end BulksketchBridge.ExecutionDriver
