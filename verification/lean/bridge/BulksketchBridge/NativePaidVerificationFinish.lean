import BulksketchBridge.NativeCanonicalCompleted
import BulksketchBridge.ReconciliationLocator
import BulksketchBridge.NativeVerificationBackendAcceptance
import BulksketchBridge.NativeVerificationReady

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 ExecutionDriverRuntime ExecutionFinish DegreeProbeRuntime
open RebuiltLfsr Reconciliation DenseCoefficient Polynomial
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish run_next)

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

private def verificationState : Bool → State
  | true => .Running .Canonicalization
  | false => .Failed .VerificationFailed

private theorem paid_frame {K : Type} (before : RootDrainState K) (input : RowInput)
    (paid : WorkMeter) (seed : Slice U64) (continued : Bool)
    (charged : StageCharge.chargeResult before.meter (ExecutionVerify.actualCost before.execution input) =
      (.Ok (), paid)) :
    let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
      (ExecutionVerify.actualCost before.execution input) seed continued
    ∃ accepted written,
      transition .Verification lower =
        (.Ok (progress .Verification before.execution),
          { before.execution with state := verificationState accepted }, written, id, paid) ∧
      written.roots = before.workspace.roots := by
  simp only [ExecutionVerify.expected, charged]
  generalize result : (if ExecutionVerify.selects before.execution input then
    ExecutionVerify.rebuiltExpected (ExecutionVerify.selectedRoots before.execution before.workspace)
      input.difference before.workspace.bm before.workspace.verification seed continued
    else
      let (accepted, updated) := ProbeVerification.expected input.difference
        (ExecutionVerify.selectedRoots before.execution before.workspace) before.workspace.verification
      (accepted, before.workspace.bm, updated)) = checked
  obtain ⟨accepted, bm, verification⟩ := checked
  cases accepted
  · exact ⟨false, _, rfl, rfl⟩
  · exact ⟨true, _, rfl, rfl⟩

def VerificationAgreement {K : Type} (before : RootDrainState K) (input : RowInput) : Prop :=
  ∀ i < input.difference.length, toField input.difference[i]!.bv =
    oddSyndrome (rootSupport (ExecutionVerify.selectedRoots before.execution before.workspace)) i

/-- Exact terminal source result starting at admitted Verification. A mismatch
stops after the paid verifier. A match pays canonicalization, preserves the
source workspace frame, and returns the sorted prefix or Equal. -/
def ActualNativePaidVerificationFinish : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    ActualPaidVerificationAccepts kernels →
    ∀ (before : RootDrainState K) (input : RowInput) (paid finalMeter : WorkMeter),
      PaidVerificationReady before input paid →
      before.execution.roots.count ≤ before.execution.budget.nonzero →
      (∀ word ∈ (ExecutionVerify.selectedRoots before.execution before.workspace).val, word.bv ≠ 0) →
      canonicalStageCharge before.execution paid = (.Ok (), finalMeter) →
      ∃ seed continued,
        let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
          (ExecutionVerify.actualCost before.execution input) seed continued
        let written := (transition .Verification lower).2.2.1
        let sorted := Aeneas.Std.DegreeProbeRuntime.sortedWords
          (ExecutionVerify.selectedRoots before.execution before.workspace)
        let reply := if before.execution.roots.count = 0#usize ∧
            before.execution.budget.total = before.execution.budget.nonzero then RowResult.Equal
          else RowResult.Decoded sorted
        (VerificationAgreement before input →
          finish RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels
            before.execution input before.workspace before.meter =
              .ok (.Ok reply, canonicalWritten before.execution written, id, finalMeter)) ∧
        (¬ VerificationAgreement before input →
          finish RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels
            before.execution input before.workspace before.meter =
              .ok (.Ok (.Failed .VerificationFailed), written, id, paid))

theorem native_paid_verification_finish : ActualNativePaidVerificationFinish := by
  intro K kernels law before input paid finalMeter ready within nonzero canonicalPaid
  obtain ⟨seed, continued, ran, iffAgreement⟩ := law before input paid ready
  obtain ⟨accepted, written, exactFrame, exactRoots⟩ := paid_frame before input paid seed continued ready.charged
  let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
    (ExecutionVerify.actualCost before.execution input) seed continued
  have frame : transition .Verification lower =
      (.Ok (progress .Verification before.execution),
        { before.execution with state := verificationState accepted }, written, id, paid) := exactFrame
  change nativeCandidateDriver nativeCanonicalize kernels before.execution input before.workspace before.meter =
    .ok (transition .Verification lower) at ran
  change (transition .Verification lower).2.1.state = .Running .Canonicalization ↔
    VerificationAgreement before input at iffAgreement
  refine ⟨seed, continued, ?_⟩
  change (_ → finish _ _ _ _ _ _ _ _ _ = .ok (_, canonicalWritten _ (transition .Verification lower).2.2.1, _, _)) ∧
    (_ → finish _ _ _ _ _ _ _ _ _ = .ok (_, (transition .Verification lower).2.2.1, _, _))
  rw [frame] at iffAgreement ran ⊢
  have step := (run_next_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize
    RootSetup.gf64Dictionary kernels before.execution input before.workspace before.meter).symm.trans ran
  cases accepted
  · simp only [verificationState, reduceCtorEq, false_iff] at iffAgreement
    refine ⟨fun agreement => (iffAgreement agreement).elim, fun _ => ?_⟩
    let failed : Execution bulksketch.field.Gf64 K := { before.execution with state := .Failed .VerificationFailed }
    let last : Exit bulksketch.field.Gf64 K := ⟨failed, written, paid, none, id⟩
    have trace : DrainTrace (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
        1 before.execution before.workspace before.meter last :=
      .continued _ _ _ .Verification _ failed written id paid 0 last ready.running step
        (.terminal failed written paid rfl)
    rw [native_finish _ _ _ _ _ _ _ _ _ 1 last ⟨1, by decide, trace⟩]
    simp only [modeled, last, failed, CompletedResult.outcome, bind_ok]
  · simp only [verificationState, eq_self, true_iff] at iffAgreement
    refine ⟨fun _ => ?_, fun mismatch => (mismatch iffAgreement).elim⟩
    let middle : Execution bulksketch.field.Gf64 K :=
      { before.execution with state := .Running .Canonicalization }
    let done : Execution bulksketch.field.Gf64 K := { before.execution with state := .Complete }
    let out := canonicalWritten middle written
    let last : Exit bulksketch.field.Gf64 K := ⟨done, out, finalMeter, none, id⟩
    have room : middle.roots.count.val ≤ written.roots.length := by rw [exactRoots]; exact ready.rootRoom
    have selected : selectedCanonicalRoots middle written =
        ExecutionVerify.selectedRoots before.execution before.workspace := by
      change prefixSlice written.roots before.execution.roots.count.val = _
      rw [exactRoots]
      rfl
    have canon := (canonical_stage_paid_iff kernels middle input written paid finalMeter
      rfl ready.noProbe canonicalPaid within room).mpr (by rw [selected]; exact ⟨nonzero, ready.distinct⟩)
    have canonStep := (run_next_refines RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize
      RootSetup.gf64Dictionary kernels middle input written paid).symm.trans canon
    have tail : DrainTrace (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
        1 middle written paid last :=
      .continued _ _ _ .Canonicalization _ done out id finalMeter 0 last rfl canonStep
        (.terminal done out finalMeter rfl)
    have trace : DrainTrace (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
        2 before.execution before.workspace before.meter last :=
      .continued _ _ _ .Verification _ middle written id paid 1 last ready.running step tail
    rw [native_finish _ _ _ _ _ _ _ _ _ 2 last ⟨2, by decide, trace⟩]
    obtain ⟨width, prefixFrame, _⟩ := canonical_stage_written middle written room
    have sortPrefix : prefixSlice out.roots before.execution.roots.count.val =
        Aeneas.Std.DegreeProbeRuntime.sortedWords
          (ExecutionVerify.selectedRoots before.execution before.workspace) := by
      rw [← selected]
      apply Slice.ext
      simpa only [prefixSlice, Slice.from_val] using prefixFrame
    have sameOut : out = canonicalWritten before.execution written := by
      unfold out canonicalWritten middle
      rfl
    unfold modeled CompletedResult.outcome
    dsimp only [last, done]
    split <;> rename_i equal
    · rw [bind_ok, sameOut]
    · unfold CompletedResult.decoded
      have bound : before.execution.roots.count.val ≤ out.roots.length := by rw [width]; exact room
      rw [ite_eq_left bound, sortPrefix, bind_ok, sameOut]

#print axioms native_paid_verification_finish


/-- A traversal that emitted the honest support locator supplies all
semantic preconditions of the paid original verifier and canonicalizer.
The source workspace admission supplies their slice bounds. -/
def ActualNativeRecoveredSupportFinish : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    ActualPaidVerificationAccepts kernels →
    ∀ (before : RootDrainState K) (input : RowInput) (support : Finset Field) (paid finalMeter : WorkMeter),
      before.execution.state = .Running .Verification → before.execution.degree_probe = none →
      WorkspaceAdmission.Admitted (RootRun.workspaceLengths before.workspace)
        input.difference.length before.execution.budget.nonzero.val →
      0 < input.difference.length → before.execution.budget.nonzero.val ≤ input.difference.length →
      before.execution.roots.count ≤ before.execution.budget.nonzero →
      (0 : Field) ∉ support → RootRun.emittedProduct before.execution.roots before.workspace = supportLocator support →
      (∀ i < input.difference.length, toField input.difference[i]!.bv = oddSyndrome support i) →
      StageCharge.chargeResult before.meter (ExecutionVerify.actualCost before.execution input) = (.Ok (), paid) →
      canonicalStageCharge before.execution paid = (.Ok (), finalMeter) →
      let sorted := Aeneas.Std.DegreeProbeRuntime.sortedWords
        (ExecutionVerify.selectedRoots before.execution before.workspace)
      let reply := if before.execution.roots.count = 0#usize ∧
          before.execution.budget.total = before.execution.budget.nonzero then RowResult.Equal
        else RowResult.Decoded sorted
      ∃ written,
        finish RootRun.nativeCalls RootRun.nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels
          before.execution input before.workspace before.meter = .ok (.Ok reply, written, id, finalMeter) ∧
        rootSupport sorted = support ∧ sorted.val.Nodup ∧ sorted.length = support.card ∧
        sorted.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧
        written.roots.val.take before.execution.roots.count.val = sorted.val

theorem native_recovered_support_finish : ActualNativeRecoveredSupportFinish := by
  classical
  intro K kernels law before input support paid finalMeter running noProbe admitted positive budgetCap
    rootBudget noZero represented syndromes charge canonCharge sorted reply
  obtain ⟨_, _, _, _, _, _, _, _, bm, _, _, _, verifyRoom, rootsRoom, _, _⟩ := admitted
  change 4 * (input.difference.length + 1) ≤ before.workspace.bm.length at bm
  change input.difference.length ≤ before.workspace.verification.length at verifyRoom
  change before.execution.budget.nonzero.val ≤ before.workspace.roots.length at rootsRoom
  have countBound : before.execution.roots.count.val ≤ before.execution.budget.nonzero.val := rootBudget
  have room : before.execution.roots.count.val ≤ before.workspace.roots.length := countBound.trans rootsRoom
  let selected := ExecutionVerify.selectedRoots before.execution before.workspace
  have selectedLen : selected.length = before.execution.roots.count.val := by
    unfold selected ExecutionVerify.selectedRoots
    rw [prefix_length, Nat.min_eq_left room]
  have polynomial : RootRun.rootsProduct selected.val = supportLocator support := by
    simpa only [selected, ExecutionVerify.selectedRoots, prefixSlice, Slice.from_val,
      RootRun.emittedProduct] using represented
  have supportRoots : (supportLocator support).roots = support.val := roots_prod_X_sub_C support
  have nonzeroRoot : ∀ point, (supportLocator support).IsRoot point → point ≠ 0 := by
    intro point isRoot zero
    subst point
    have present := (mem_roots (supportLocator_monic support).ne_zero).mpr isRoot
    rw [supportRoots] at present
    exact noZero present
  obtain ⟨nonzero, distinct⟩ := RootRun.emitted_words_valid selected.val (supportLocator support) polynomial
    (supportRoots.symm ▸ support.nodup) nonzeroRoot
  have exactSupport : rootSupport selected = support := by
    have exactMultiset : ((selected.val.map fun word => toField word.bv) : Multiset Field) = support.val := by
      rw [← RootRun.roots_product_roots, polynomial, supportRoots]
    rw [rootSupport, ← List.toFinset_coe, exactMultiset, Finset.val_toFinset]
  have ready : PaidVerificationReady before input paid := by
    refine ⟨running, noProbe, charge, room, distinct, fun _ => ?_, fun _ => ⟨fun _ => positive, fun _ => verifyRoom⟩⟩
    change (0 : Field) ∉ rootSupport selected ∧ selected.length < before.workspace.bm.length ∧
      min selected.length input.difference.length ≤ before.workspace.verification.length
    rw [exactSupport, selectedLen]
    exact ⟨noZero, by omega, (Nat.min_le_right ..).trans verifyRoom⟩
  have agreement : VerificationAgreement before input := by
    unfold VerificationAgreement
    rw [show rootSupport (ExecutionVerify.selectedRoots before.execution before.workspace) = support from exactSupport]
    exact syndromes
  obtain ⟨seed, continued, matched, _⟩ := native_paid_verification_finish kernels law before input paid finalMeter
    ready rootBudget nonzero canonCharge
  let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
    (ExecutionVerify.actualCost before.execution input) seed continued
  let verified := (transition .Verification lower).2.2.1
  have sameRootWords : verified.roots = before.workspace.roots := by
    obtain ⟨accepted, written, frame, same⟩ := paid_frame before input paid seed continued charge
    change transition .Verification lower = _ at frame
    unfold verified
    rw [frame]
    exact same
  have writtenRoom : before.execution.roots.count.val ≤ verified.roots.length := by rw [sameRootWords]; exact room
  obtain ⟨_, prefixFrame, _⟩ := canonical_stage_written before.execution verified writtenRoom
  have sortedEq : sorted = Aeneas.Std.DegreeProbeRuntime.sortedWords selected := rfl
  have permutation := DegreeProbeRuntime.sortedWords_perm selected
  have sortedSupport : rootSupport sorted = support := by
    rw [← exactSupport]
    apply Finset.ext
    intro point
    simp only [rootSupport, List.mem_toFinset, sortedEq]
    exact (permutation.map _).mem_iff
  have sortedDistinct : sorted.val.Nodup := by rw [sortedEq]; exact permutation.nodup_iff.mpr distinct
  refine ⟨canonicalWritten before.execution verified, matched agreement, sortedSupport, sortedDistinct,
    (rootSupport_card sorted sortedDistinct).symm.trans (congrArg Finset.card sortedSupport),
    DegreeProbeRuntime.sortedWords_ordered selected, ?_⟩
  rw [prefixFrame]
  change (Aeneas.Std.DegreeProbeRuntime.sortedWords
      (prefixSlice verified.roots before.execution.roots.count.val)).val = sorted.val
  rw [sameRootWords]
  rfl

#print axioms native_recovered_support_finish

end BulksketchBridge.ExecutionDriver
