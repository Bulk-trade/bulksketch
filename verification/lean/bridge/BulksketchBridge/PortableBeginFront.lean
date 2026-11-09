import BulksketchBridge.PortableFrontPayment
import BulksketchBridge.ConcreteRebuiltDictionaries
import BulksketchBridge.RowConfiguration
import BulksketchBridge.ReconstructionPowerSums
import BulksketchBridge.RankedExecutionChunks
import BulksketchBridge.RankedRootDrainAdapter
import BulksketchBridge.NativeCanonicalizeDriver

namespace BulksketchBridge.PortableBeginFront

open Aeneas.Std Algebra.Gf64 Polynomial Reconciliation RebuiltLfsr DenseCoefficient SliceKernels
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish PortableFrontPayment
open bulksketch.decode.stages bulksketch.decode.row bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.BinaryDecoder.Insts.BulksketchDecodeRowRowDecoderFKExecution (begin)
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)

set_option maxRecDepth 4096
set_option maxHeartbeats 5000000

abbrev Backend := bulksketch.backend.portable.Portable
abbrev Point := RootDrainState Backend

def frontWork (capacity : Nat) (budget : Usize) : Nat :=
  3 * capacity + max 1 (2 * capacity) * BmPrice.bmUnits budget

abbrev start (budget : RowBudget) (workspace : RowWorkspace) (meter : WorkMeter) : Point :=
  ⟨RowConfiguration.initialExecution budget, workspace, meter⟩

abbrev atCandidates (budget : RowBudget) (degree : Usize) (workspace : RowWorkspace)
    (meter : WorkMeter) : Point :=
  ⟨{ RowConfiguration.initialExecution budget with state := .Running .CandidateEvaluation, degree },
    workspace, meter⟩

private theorem zero_row_support (support : Finset Field) (difference : Slice U64)
    (nonzero : (0 : Field) ∉ support) (card : support.card ≤ difference.length)
    (oddWords : ∀ i < difference.length, toField difference.val[i]!.bv = oddSyndrome support i)
    (zero : Reconstruction.allZero difference = true) : support = ∅ := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  apply eq_of_oddSyndromes_eq difference.length support ∅ card (by simp) nonzero (by simp)
  intro i active
  have word := (Reconstruction.all_zero_iff difference).mp zero difference.val[i]! (by
    rw [List.getElem!_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (show i < difference.val.length from active)]
    exact List.getElem_mem _)
  rw [← oddWords i active, word]
  change toField (0 : BitVec 64) = oddSyndrome ∅ i
  rw [toField_zero]
  simp only [oddSyndrome, powerSum, Finset.sum_empty]

private theorem run_reconstruct (self : Execution bulksketch.field.Gf64 Backend) (input : RowInput)
    (workspace : RowWorkspace) (meter : WorkMeter) (lower : Frame bulksketch.field.Gf64 Backend)
    (running : self.state = .Running .Reconstruction) (noProbe : self.degree_probe = none)
    (ran : Execution.reconstruct portableField portableKernels self input workspace meter = .ok lower) :
    nativeCandidateDriver nativeCanonicalize portableKernels self input workspace meter =
      .ok (transition .Reconstruction lower) := by
  apply run_next_return RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
    portableKernels self .Reconstruction input workspace meter lower running
  rw [execute_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
    portableKernels self .Reconstruction input workspace meter, expectedExecute, noProbe]
  exact ran

/-- Original Portable begin, reconstruction and BM either take the exact
zero-work Equal branch or advance the original driver with the honest locator.
All later root configuration fields stay as initialized by the source begin. -/
def ActualPortableBeginFront : Prop :=
  ∀ (budget : RowBudget) (input : RowInput) (workspace : RowWorkspace) (meter : WorkMeter)
    (support : Finset Field),
    (0 : Field) ∉ support → support.card ≤ budget.nonzero.val →
    budget.nonzero.val ≤ input.difference.length →
    WorkspaceAdmission.Admitted (RootRun.workspaceLengths workspace)
      input.difference.length budget.nonzero.val →
    (∀ i < input.difference.length, toField input.difference.val[i]!.bv = oddSyndrome support i) →
    meter.exhausted = false → meter.used.val + frontWork input.difference.length budget.nonzero ≤ meter.limit.val →
    begin portableField portableKernels budget = .ok (start budget workspace meter).execution ∧
    ((support = ∅ ∧ budget.total = budget.nonzero ∧
      finish RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize portableField portableKernels
        (start budget workspace meter).execution input workspace meter = .ok (.Ok .Equal, workspace, id, meter)) ∨
    ∃ degree written paid,
      SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) portableField portableKernels input
        2 (start budget workspace meter) (atCandidates budget degree written paid) id ∧
      degree.val = support.card ∧
      slicePolynomial (prefixSlice written.bm (degree.val + 1)) = supportLocator support ∧
      RootRun.ValidFactor (slicePolynomial (prefixSlice written.bm (degree.val + 1))) degree.val ∧
      RootRun.workspaceLengths written = RootRun.workspaceLengths workspace ∧
      paid.exhausted = false ∧ paid.limit = meter.limit ∧
      paid.used.val ≤ meter.used.val + frontWork input.difference.length budget.nonzero)

theorem portable_begin_front : ActualPortableBeginFront := by
  intro budget input workspace meter support nonzero card bounded admitted oddWords live reserve
  refine ⟨RowConfiguration.begin_refines portableField portableKernels budget, ?_⟩
  let self : Execution bulksketch.field.Gf64 Backend := RowConfiguration.initialExecution budget
  have square (word : U64) :
      portableKernels.ArithmeticInst.square word = .ok (Reconstruction.squareWord word) :=
    Square.square_refines word
  obtain ⟨reply, updated, final, exactRun, outcome⟩ :=
    Reconstruction.reconstruct_refines portableField portableKernels self input workspace meter square
  by_cases early : budget.total = budget.nonzero ∧ Reconstruction.allZero input.difference = true
  · have earlySelf : self.budget.total = self.budget.nonzero ∧ Reconstruction.allZero input.difference = true := early
    simp only [earlySelf] at outcome
    obtain ⟨same, modeled, replied⟩ := outcome
    subst updated
    have enough : meter.used.val ≤ meter.limit.val := by omega
    have zero := BulksketchProofs.Resource.WorkMeter.zero_charge (WorkMeter.toModel meter) live
      (by simpa only [BulksketchProofs.Resource.WorkMeter.Bounded, WorkMeter.toModel, WorkMeter.toUInt64_toNat] using enough)
    rw [zero] at modeled replied
    have finalEq : final = meter := WorkMeter.toModel_injective modeled
    subst final
    have success : reply = .Ok (.Ok none) := replied
    subst reply
    have run := run_reconstruct self input workspace meter _ rfl rfl exactRun
    let done : Execution bulksketch.field.Gf64 Backend := {self with state := .Complete}
    let terminal : Exit bulksketch.field.Gf64 Backend := ⟨done, workspace, meter, none, id⟩
    have trace : DrainTrace (nativeDrainRuntime nativeCanonicalize) portableField portableKernels input
        1 self workspace meter terminal :=
      .continued _ _ _ .Reconstruction _ done workspace id meter 0 terminal rfl
        ((run_next_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize portableField
          portableKernels self input workspace meter).symm.trans run)
        (.terminal done workspace meter rfl)
    refine Or.inl ⟨zero_row_support support input.difference nonzero (card.trans bounded) oddWords early.2, early.1, ?_⟩
    change finish RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize portableField portableKernels
      self input workspace meter = _
    rw [native_finish _ _ _ _ _ _ _ _ _ 1 terminal ⟨1, by decide, trace⟩]
    simp only [ExecutionFinish.modeled, terminal, done, self, RowConfiguration.initialExecution, RowConfiguration.initialRoots,
      CompletedResult.outcome, early.1, eq_self, true_and, ite_true, bind_ok]
  · have earlySelf : ¬ (self.budget.total = self.budget.nonzero ∧
        Reconstruction.allZero input.difference = true) := early
    have canPay : meter.used.val + 3 * input.difference.length ≤ meter.limit.val := by
      unfold frontWork at reserve
      omega
    obtain ⟨paid, paidReconstruction, firstUsed, firstLimit, firstLive⟩ :=
      pay_units meter (3 * input.difference.length) live canPay
    have paidSource : StageCharge.reconstructCharge meter input.difference.len = (.Ok (), paid) := by
      unfold StageCharge.reconstructCharge WorkSchedule.reconstructCost
      rw [Slice.len_val]
      exact paidReconstruction
    have passes : WorkspaceAdmission.check (Reconstruction.workspaceLengths workspace)
        input.difference.length self.budget.nonzero.val = true := by
      unfold WorkspaceAdmission.check
      exact decide_eq_true admitted
    simp only [earlySelf, ite_false, paidSource, Reconstruction.PaidOutcome, passes, ite_true] at outcome
    obtain ⟨sameFinal, sameReply, syndromes, sameWorkspace, reconstructed⟩ := outcome
    subst final reply updated
    let written := { workspace with syndromes }
    let middle : Point := ⟨{ self with state := .Running .BerlekampMassey }, written, paid⟩
    have firstStep := run_reconstruct self input workspace meter _ rfl rfl exactRun
    obtain ⟨_, _, _, _, _, _, _, syndromeRoom, bmRoom, _⟩ := admitted
    have moments : BmHonestLocator.Moments support syndromes (2 * input.difference.length) := by
      intro i positive within
      rw [Slice.getElem!_Nat_eq]
      exact Reconstruction.prefix_represents_power_sums support input.difference workspace.syndromes
        syndromes oddWords reconstructed i positive within
    have bmBound : 3 * (input.difference.length + 1) ≤ written.bm.length := by
      change 4 * (input.difference.length + 1) ≤ workspace.bm.length at bmRoom
      change 3 * (input.difference.length + 1) ≤ workspace.bm.length
      omega
    have powerRoom : 2 * input.difference.length + 1 ≤ syndromes.length := by
      rw [reconstructed.length]
      exact syndromeRoom
    obtain ⟨bmReply, locatorRun, sameWidth, bmOutcome⟩ :=
      native_honest_bm_driver nativeCanonicalize portableKernels (fun _ _ => rfl) (fun _ => rfl)
        (fun _ _ => rfl) (fun _ => rfl) middle.execution input written workspace.syndromes paid support
        rfl rfl nonzero card bounded bmBound powerRoom reconstructed moments
    have bmFits : paid.used.val + max 1 (2 * input.difference.len.val) *
        BmPrice.bmUnits budget.nonzero ≤ paid.limit.val := by
      rw [Slice.len_val, firstUsed, firstLimit, Nat.add_assoc]
      exact reserve
    obtain ⟨degree, succeeded, finalLive, finalLimit, debit⟩ :=
      bm_reply_paid portableKernels (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
        support syndromes written.bm input.difference workspace.syndromes input.difference.len budget.nonzero
        paid bmReply nonzero card (by rwa [Slice.len_val]) (by rwa [Slice.len_val]) (by rwa [Slice.len_val])
        (by rwa [Slice.len_val]) (by rwa [Slice.len_val]) firstLive bmFits locatorRun
    simp only [succeeded] at bmOutcome
    obtain ⟨secondStep, degreeEq, locator, valid⟩ := bmOutcome
    let output := { written with bm := bmReply.2.1 }
    let after := atCandidates budget degree output bmReply.2.2
    have tail : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) portableField portableKernels input
        1 middle after id :=
      .step middle after after .BerlekampMassey (progress .BerlekampMassey {middle.execution with degree})
        id id 0 rfl secondStep (.empty after)
    have chunk : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) portableField portableKernels input
        2 (start budget workspace meter) after id :=
      .step (start budget workspace meter) middle after .Reconstruction (progress .Reconstruction self)
        id id 1 rfl firstStep tail
    refine Or.inr ⟨degree, output, bmReply.2.2, chunk, degreeEq, locator, valid, ?_,
      finalLive, finalLimit.trans firstLimit, ?_⟩
    · simp only [output, written, RootRun.workspaceLengths, reconstructed.length, sameWidth]
    · rwa [Slice.len_val, firstUsed, Nat.add_assoc] at debit

#print axioms portable_begin_front

end BulksketchBridge.PortableBeginFront
