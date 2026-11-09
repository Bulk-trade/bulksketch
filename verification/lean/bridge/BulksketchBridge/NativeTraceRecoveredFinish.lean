import BulksketchBridge.NativeTraceDrain
import BulksketchBridge.NativePaidVerificationFinish
import BulksketchBridge.RowWorkBudgetV3VerifierQuotes

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial RootWorkBudget RootTrace DenseCoefficient SliceKernels
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec Reconciliation RebuiltLfsr
open ExecutionDriver ExecutionDriverRuntime ExecutionFinish WorkSchedule
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)
open AffineSelector (word word_val)

set_option maxRecDepth 4096
set_option maxHeartbeats 5500000

def verificationReserve (capacity degree : Nat) (beta : Usize) : Nat :=
  max (originalVerifyUnits capacity beta.val) (rebuiltVerifyUnits capacity degree beta.val) +
    CanonicalizePrice.units beta

private theorem paid_model_charge (meter : WorkMeter) (amount : U64)
    (live : meter.exhausted = false) (room : meter.used.val + amount.val ≤ meter.limit.val) :
    ∃ paid, StageCharge.chargeResult meter (.Ok amount) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + amount.val ∧ paid.limit = meter.limit ∧ paid.exhausted = false := by
  obtain ⟨paid, charged, used, limit, active⟩ := WorkMeter.native_work_meter_paid meter amount live room
  rw [StageCharge.meter_charge_refines] at charged
  exact ⟨paid, Result.ok_injective charged, used, limit, active⟩

/-- An admitted plain, non-affine root frontier drains through the
original native finish and returns the exact honest support. The
frontier and tail reservation suffice for every source charge. -/
def ActualNativeTraceRecoveredFinish : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → DirectTwo.CorrectArithmetic kernels →
    ActualPaidVerificationAccepts kernels →
    ∀ (support : Finset Field) (input : RowInput) (before : RootDrainState K),
      let capacity := input.difference.length
      let budget := before.execution.budget.nonzero.val
      let beta := before.execution.budget.total
      0 < capacity → capacity ≤ 65535 → budget ≤ capacity → beta.val ≤ 65535 →
      (0 : Field) ∉ support → (∀ i < capacity, toField input.difference[i]!.bv = oddSyndrome support i) →
      NativeTraceFrontier (supportLocator support) before capacity budget →
      before.meter.used.val + frontierWork before.execution.roots before.workspace.stack +
        verificationReserve capacity support.card beta ≤ before.meter.limit.val →
      ∃ (sorted : Slice U64) (written : RowWorkspace) (paid : WorkMeter),
        let reply := if support.card = 0 ∧ beta = before.execution.budget.nonzero then RowResult.Equal
          else RowResult.Decoded sorted
        finish nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels before.execution
          input before.workspace before.meter = .ok (.Ok reply, written, id, paid) ∧
        rootSupport sorted = support ∧ sorted.val.Nodup ∧ sorted.length = support.card ∧
        sorted.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧
        written.roots.val.take support.card = sorted.val ∧
        paid.limit = before.meter.limit ∧ paid.exhausted = false ∧
        paid.used.val ≤ before.meter.used.val + frontierWork before.execution.roots before.workspace.stack +
          verificationReserve capacity support.card beta

/-- An admitted plain, non-affine root frontier drains through the
original native finish and returns the exact honest support. The
frontier and tail reservation suffice for every source charge. -/
def ActualNativeTraceRecoveredAfterPrefix : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → DirectTwo.CorrectArithmetic kernels →
    ActualPaidVerificationAccepts kernels →
    ∀ (support : Finset Field) (input : RowInput) (before : RootDrainState K),
      let capacity := input.difference.length
      let budget := before.execution.budget.nonzero.val
      let beta := before.execution.budget.total
      0 < capacity → capacity ≤ 65535 → budget ≤ capacity → beta.val ≤ 65535 →
      (0 : Field) ∉ support → (∀ i < capacity, toField input.difference[i]!.bv = oddSyndrome support i) →
      NativeTraceFrontier (supportLocator support) before capacity budget →
      before.meter.used.val + frontierWork before.execution.roots before.workspace.stack +
        verificationReserve capacity support.card beta ≤ before.meter.limit.val →
      ∀ (initial : RootDrainState K) (prefixSteps : Nat),
        SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
          prefixSteps initial before id →
      ∃ (sorted : Slice U64) (written : RowWorkspace) (paid : WorkMeter),
        let reply := if support.card = 0 ∧ beta = before.execution.budget.nonzero then RowResult.Equal
          else RowResult.Decoded sorted
        finish nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels initial.execution
          input initial.workspace initial.meter = .ok (.Ok reply, written, id, paid) ∧
        rootSupport sorted = support ∧ sorted.val.Nodup ∧ sorted.length = support.card ∧
        sorted.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧
        written.roots.val.take support.card = sorted.val ∧
        paid.limit = before.meter.limit ∧ paid.exhausted = false ∧
        paid.used.val ≤ before.meter.used.val + frontierWork before.execution.roots before.workspace.stack +
          verificationReserve capacity support.card beta

theorem native_trace_recovered_after_prefix : ActualNativeTraceRecoveredAfterPrefix := by
  intro K kernels scale backend raw square reduce mul inverse arithmetic accept support input before
    capacity budget beta positive capFit budgetCap betaFit nonzero syndromes ready reserve initial prefixSteps prefixChunk
  obtain ⟨steps, final, _, segment, emitted, sameBudget, sameLimit, _, spent⟩ :=
    native_trace_drain nativeCanonicalize kernels scale backend raw square reduce mul inverse arithmetic
      (supportLocator support) input before capacity budget (budgetCap.trans capFit) ready
  have degree : final.execution.roots.count.val = support.card :=
    emitted.count.trans (supportLocator_natDegree support)
  have supportFit : support.card ≤ budget := by
    rw [← supportLocator_natDegree support]
    exact ready.traversal.degreeBudget
  have rootBudget : final.execution.roots.count ≤ final.execution.budget.nonzero := by
    change final.execution.roots.count.val ≤ final.execution.budget.nonzero.val
    rw [degree, sameBudget]
    exact supportFit
  have capWord : input.difference.len.val = capacity := Slice.len_val ..
  have betaWord : final.execution.budget.total = beta := congrArg RowBudget.total sameBudget
  obtain ⟨full, rebuilt, fullFit, rebuiltFit⟩ := native_v3_verifier_quotes
    input.difference.len final.execution.roots.count final.execution.budget.total
    (capWord.symm ▸ capFit) (by rw [degree]; omega) (betaWord.symm ▸ betaFit)
  simp only [capWord, degree, betaWord] at full rebuilt fullFit rebuiltFit
  have price : ∃ amount, ExecutionVerify.actualCost final.execution input = .Ok amount ∧
      amount.val ≤ max (originalVerifyUnits capacity beta.val) (rebuiltVerifyUnits capacity support.card beta.val) := by
    have actual := ExecutionVerify.actual_cost_refines final.execution input
    unfold ExecutionVerify.priceTag at actual
    rw [betaWord] at actual
    cases selected : ExecutionVerify.selects final.execution input
    · simp only [selected, Bool.false_eq_true, ite_false] at actual
      rw [full] at actual
      refine ⟨_, Result.ok_injective actual.symm, ?_⟩
      rw [word_val _ (by omega : originalVerifyUnits capacity beta.val ≤ U64.max)]
      exact Nat.le_max_left ..
    · simp only [selected, ite_true] at actual
      rw [rebuilt] at actual
      refine ⟨_, Result.ok_injective actual.symm, ?_⟩
      rw [word_val _ rebuiltFit]
      exact Nat.le_max_right ..
  obtain ⟨amount, exactPrice, priceBound⟩ := price
  have remaining : final.meter.used.val + amount.val + CanonicalizePrice.units beta ≤ final.meter.limit.val := by
    rw [sameLimit]
    unfold verificationReserve at reserve
    omega
  obtain ⟨paid, first, firstUsed, firstLimit, firstLive⟩ :=
    paid_model_charge final.meter amount emitted.live (by omega)
  have canonicalRoom : paid.used.val + CanonicalizePrice.units beta ≤ paid.limit.val := by
    rw [firstUsed, firstLimit]
    exact remaining
  have fits : CanonicalizePrice.units beta ≤ U64.max := by
    have bound := paid.limit.le_max
    rw [U64.max_eq] at *
    omega
  have priced : checkedCost (CanonicalizePrice.units beta) = .Ok (word (CanonicalizePrice.units beta)) :=
    (checked_cost_ok_iff _ _).mpr ⟨fits, word_val _ fits⟩
  obtain ⟨charged, second, secondUsed, secondLimit, secondLive⟩ :=
    paid_model_charge paid (word (CanonicalizePrice.units beta)) firstLive (by rwa [word_val _ fits])
  have firstCharge : StageCharge.chargeResult final.meter (ExecutionVerify.actualCost final.execution input) =
      (.Ok (), paid) := by rwa [exactPrice]
  have canonicalCharge : canonicalStageCharge final.execution paid = (.Ok (), charged) := by
    unfold canonicalStageCharge
    rwa [betaWord, priced]
  have workspace : WorkspaceAdmission.Admitted (workspaceLengths final.workspace)
      input.difference.length final.execution.budget.nonzero.val := by rw [sameBudget]; exact emitted.workspace
  have finalBudget : final.execution.budget.nonzero.val ≤ input.difference.length := by rw [sameBudget]; exact budgetCap
  have joined := append_successful_chunks prefixChunk segment
  obtain ⟨written, result, supportEq, distinct, length, ordered, writtenPrefix⟩ :=
    native_recovered_support_after_chunk kernels accept final input support paid charged emitted.state
      emitted.noProbe workspace positive finalBudget rootBudget nonzero emitted.factor syndromes firstCharge
      canonicalCharge initial (prefixSteps + steps) joined
  have empty : final.execution.roots.count = 0#usize ↔ support.card = 0 := by
    constructor
    · intro zero
      rw [← degree, zero]
      rfl
    · intro zero
      exact UScalar.eq_of_val_eq (degree.trans zero)
  refine ⟨_, written, charged, ?_, supportEq, distinct, length, ordered, ?_, ?_, secondLive, ?_⟩
  · simpa only [empty, sameBudget] using result
  · simpa only [degree] using writtenPrefix
  · exact secondLimit.trans (firstLimit.trans sameLimit)
  · rw [secondUsed, firstUsed, word_val _ fits]
    unfold verificationReserve
    omega

#print axioms native_trace_recovered_after_prefix

theorem native_trace_recovered_finish : ActualNativeTraceRecoveredFinish := by
  intro K kernels scale backend raw square reduce mul inverse arithmetic accept support input before
    capacity budget beta positive capFit budgetCap betaFit nonzero syndromes ready reserve
  exact native_trace_recovered_after_prefix kernels scale backend raw square reduce mul inverse arithmetic accept
    support input before positive capFit budgetCap betaFit nonzero syndromes ready reserve before 0 (.empty before)

#print axioms native_trace_recovered_finish

end BulksketchBridge.RootRun
