import BulksketchBridge.ExecutionDispatch
import BulksketchBridge.NativeRootRun
import BulksketchBridge.CandidateSuccessHandoff
import BulksketchBridge.CandidateHornerBridge
import BulksketchBridge.RootEmissionProduct
import BulksketchBridge.NativeDeflateTraversalEntry

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std ExecutionDriverRuntime Algebra.Gf64 Polynomial DenseCoefficient SliceKernels
open CandidateOuter Deflation
open bulksketch.backend.contract bulksketch.decode.row bulksketch.decode.stages
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (run_next)

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem run_next_return {F K : Type} (calls : RootRunRuntime.OtherCallees)
    (division : DenseDivisionRuntime.DivRem) (canonicalize : Canonicalize)
    (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Execution F K) (stage : Stage) (input : RowInput) (workspace : RowWorkspace)
    (meter : WorkMeter) (lower : Frame F K) (state : self.state = .Running stage)
    (ran : Execution.execute calls division canonicalize field kernels self stage input workspace meter = .ok lower) :
    run_next calls division canonicalize field kernels self input workspace meter = .ok (transition stage lower) := by
  rw [run_next_refines calls division canonicalize field kernels self input workspace meter,
    expectedRunNext, state]
  dsimp only
  rw [ran, bind_ok]

abbrev nativeCandidateDriver {K : Type} (canonicalize : Canonicalize) (kernels : BulkKernels K bulksketch.field.Gf64) :=
  run_next RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary kernels

private theorem candidates_driver {K : Type} (canonicalize : Canonicalize) (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter)
    (lower : Frame bulksketch.field.Gf64 K) (state : self.state = .Running .CandidateEvaluation)
    (probe : self.degree_probe = none)
    (ran : Execution.candidates RootSetup.gf64Dictionary kernels self input workspace meter = .ok lower) :
    nativeCandidateDriver canonicalize kernels self input workspace meter = .ok (transition .CandidateEvaluation lower) := by
  apply run_next_return RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels self .CandidateEvaluation input workspace meter lower state
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels self .CandidateEvaluation input workspace meter, expectedExecute, probe]
  exact ran

private theorem deflate_driver {K : Type} (canonicalize : Canonicalize) (kernels : BulkKernels K bulksketch.field.Gf64)
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter)
    (lower : Frame bulksketch.field.Gf64 K) (state : self.state = .Running .Deflation)
    (probe : self.degree_probe = none)
    (ran : Execution.deflate RootSetup.gf64Dictionary kernels self input workspace meter = .ok lower) :
    nativeCandidateDriver canonicalize kernels self input workspace meter = .ok (transition .Deflation lower) := by
  apply run_next_return RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels self .Deflation input workspace meter lower state
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem canonicalize RootSetup.gf64Dictionary
    kernels self .Deflation input workspace meter, expectedExecute, probe]
  exact ran

/-- Two consecutive original run_next calls enter traversal with the exact
    admitted residual factor and previously emitted roots. The source
    execution state is latched at each returned stage. -/
def ActualNativeCandidateDeflateDriver : Prop :=
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
      original = RootRun.emittedProduct updated written * residual ∧
      RootRun.activeTraversalProduct updated written = original ∧
      final.degree.val + count.val = self.degree.val ∧ updated.count = count ∧ updated.pending = 0#usize ∧
      RootRun.BudgetBuffers written input.difference.length self.budget.nonzero.val ∧
      RootRun.PendingLayout updated written.stack written.factors.length written.polynomials.length ∧
      RootRun.factorDegreeMass updated written.stack = self.degree.val ∧
      (final.degree ≠ 0#usize → RootRun.activeFactor updated written = residual) ∧
      residual.Monic ∧ residual.natDegree = final.degree.val ∧ residual.Splits ∧ residual.roots.Nodup ∧
      (∀ point, residual.IsRoot point → point ≠ 0) ∧
      (∀ j, j < count.val → ¬ residual.IsRoot (toField (deflateHits next scanned)[j]!.bv))

theorem native_candidate_deflate_driver : ActualNativeCandidateDeflateDriver := by
  intro canonicalize K kernels horner mul self input workspace meter finalMeter state probe admitted
    positive cap degreeBudget pending fresh unique original monic degree split simple nonzero charge paid deflatePaid
  obtain ⟨count, roots, values, candidateRan, handoff, meaning⟩ :=
    native_candidate_success_handoff kernels (candidate_horner_of_polynomial kernels horner)
      self input workspace meter admitted cap degreeBudget
      pending fresh unique monic degree split simple nonzero paid
  let candidate := completedExecution self count false
  let next := { candidate with state := .Running .Deflation }
  let scanned := candidateWorkspace input workspace roots values
  obtain ⟨budgetCap, boundedDegree, hitBound, exactCount, emptyPending, writtenAdmitted⟩ := handoff
  obtain ⟨locatorMonic, locatorDegree, locatorSplit, locatorSimple, locatorNonzero, supplied, distinct⟩ := meaning
  have nextHandoff : DeflateCandidateHandoff next input scanned :=
    ⟨budgetCap, boundedDegree, hitBound, exactCount, emptyPending, writtenAdmitted⟩
  have nextMeaning : DeflateCandidateMeaning next input scanned :=
    ⟨locatorMonic, locatorDegree, locatorSplit, locatorSimple, locatorNonzero, supplied, distinct⟩
  have nextProbe : next.degree_probe = none := probe
  obtain ⟨final, _, balance, product, deflated, _, emptied, counted, _, _, _, rootFrame, _, _, _, mass, _,
    sized, layout, _, active, residualMonic, residualDegree, residualSplit, residualSimple, residualNonzero, disjoint⟩ :=
    native_deflate_traversal_entry RootSetup.gf64Dictionary kernels mul next input scanned charge.2 finalMeter
      nextHandoff nextMeaning positive deflatePaid
  have bm : 4 * (input.difference.length + 1) ≤ workspace.bm.length := admitted.2.2.2.2.2.2.2.2.1
  have sameLocator : initialDeflateLocator next input scanned = original := by
    unfold initialDeflateLocator activeLocator
    change slicePolynomial (prefixSlice (prefixSlice scanned.bm (input.difference.length + 1))
      (self.degree.val + 1)) = _
    rw [candidate_locator_frame input workspace roots values (by omega), ClosedLeaf.prefix_prefix]
    omega
  let joined := joinedWorkspace (deflateFrame next scanned (input.difference.length + 1))
    final.locator final.quotient
  let written := RootSetup.startedWorkspace final.degree joined
  let updated := finishedRoots next.roots final.degree
  let residual := activeLocator final.locator final.degree
  have countFits : count.val ≤ scanned.roots.length := by
    have rootsRoom := writtenAdmitted.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    change self.budget.nonzero.val ≤ scanned.roots.length at rootsRoom
    exact hitBound.trans (degreeBudget.trans rootsRoom)
  have hitWidth : (deflateHits next scanned).length = count.val := by
    change (prefixSlice scanned.roots count.val).length = _
    rw [RebuiltLfsr.prefix_length, Nat.min_eq_left countFits]
  have nextHits : next.hits = count := rfl
  have emitted : rootProduct (deflateHits next scanned) 0 count.val = RootRun.emittedProduct updated written := by
    rw [RootRun.deflate_root_product_words _ _ _ (by rw [Nat.zero_add, hitWidth])]
    unfold RootRun.emittedProduct
    change updated.count = count at counted
    rw [counted, rootFrame, List.drop_zero]
    simp only [deflateHits, prefixSlice, Slice.from_val, List.take_take, nextHits, Nat.min_self]
  have exactProduct : original = RootRun.emittedProduct updated written * residual := by
    change initialDeflateLocator next input scanned = rootProduct (deflateHits next scanned) 0 count.val * residual at product
    rw [sameLocator, emitted] at product
    exact product
  have represented := RootRun.initial_traversal_product original residual updated written emptied
    exactProduct residualMonic residualDegree active
  refine ⟨count, roots, values, final, ?_, ?_, exactProduct, represented, balance, counted, emptied,
    sized, layout, mass, active, residualMonic, residualDegree, residualSplit, residualSimple, residualNonzero, disjoint⟩
  · exact candidates_driver canonicalize kernels self input workspace meter _ state probe candidateRan
  · exact deflate_driver canonicalize kernels next input scanned charge.2 _ rfl nextProbe deflated

#print axioms native_candidate_deflate_driver

end BulksketchBridge.ExecutionDriver
