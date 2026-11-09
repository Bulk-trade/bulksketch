import BulksketchBridge.NativeCandidateDeflateDriver
import BulksketchBridge.NativeTraceRecoveredFinish
import BulksketchBridge.NativeTraversalAdmission

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 DenseCoefficient Polynomial RootRun RootWorkBudget SliceKernels
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec Reconciliation RebuiltLfsr
open ExecutionDriverRuntime ExecutionFinish WorkSchedule CandidateOuter Deflation
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)
open AffineSelector (word word_val)

set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

/-- Candidate evaluation is free with no hints. Deflation is priced by
the original locator degree, even when no roots have been deflated. -/
def plainCandidateWork (capacity degree : Nat) (beta : Usize) : Nat :=
  2 * degree * (degree + 1) + rootsEnvelope degree + verificationReserve capacity degree beta

private theorem candidate_no_hints (degree : Usize) (input : RowInput)
    (degreeMax : degree.val ≤ 65535) (noHints : input.candidates.val = []) :
    candidateCost degree input.candidates.len = .Ok 0#u64 := by
  have noInputs : input.candidates.len.val = 0 := by simp [noHints]
  have zero : checkedCost 0 = .Ok 0#u64 :=
    (checked_cost_ok_iff _ _).mpr ⟨Nat.zero_le _, rfl⟩
  have width : degree.val + 1 ≤ U64.max := by rw [U64.max_eq]; omega
  have priced : checkedCost (degree.val + 1) = .Ok (word (degree.val + 1)) :=
    (checked_cost_ok_iff _ _).mpr ⟨width, word_val _ width⟩
  simp only [candidateCost, noInputs, Nat.mul_zero, zero, priced, show (0#u64).val = 0 from rfl, Nat.zero_mul]

private theorem pay_checked (meter : WorkMeter) (units : Nat) (live : meter.exhausted = false)
    (room : meter.used.val + units ≤ meter.limit.val) :
    ∃ paid, StageCharge.chargeResult meter (checkedCost units) = (.Ok (), paid) ∧
      paid.used.val = meter.used.val + units ∧ paid.limit = meter.limit ∧ paid.exhausted = false := by
  have fits : units ≤ U64.max := by have := meter.limit.le_max; rw [U64.max_eq] at *; omega
  have priced : checkedCost units = .Ok (word units) :=
    (checked_cost_ok_iff _ _).mpr ⟨fits, word_val _ fits⟩
  obtain ⟨paid, ran, used, limit, active⟩ :=
    WorkMeter.native_work_meter_paid meter (word units) live (by rwa [word_val _ fits])
  rw [StageCharge.meter_charge_refines] at ran
  exact ⟨paid, priced.symm ▸ Result.ok_injective ran, by rwa [word_val _ fits] at used, limit, active⟩

private theorem no_hints_paid (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
    (meter : WorkMeter) (degreeMax : self.degree.val ≤ 65535)
    (noHints : input.candidates.val = []) (live : meter.exhausted = false)
    (room : meter.used.val ≤ meter.limit.val) :
    let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
    charge.1 = .Ok () ∧ charge.2.used = meter.used ∧ charge.2.limit = meter.limit ∧ charge.2.exhausted = false := by
  dsimp only
  rw [candidate_no_hints self.degree input degreeMax noHints]
  obtain ⟨paid, ran, used, limit, active⟩ := WorkMeter.native_work_meter_paid meter 0#u64 live (by simpa using room)
  rw [StageCharge.meter_charge_refines] at ran
  rw [Result.ok_injective ran]
  exact ⟨rfl, UScalar.eq_of_val_eq (by simpa using used), limit, active⟩

/-- The successful honest candidate stage keeps the original initial
non-affine traversal controls. -/
structure PlainCandidate {K : Type} (point : RootDrainState K) (input : RowInput)
    (support : Finset Field) : Prop where
  state : point.execution.state = .Running .CandidateEvaluation
  noProbe : point.execution.degree_probe = none
  scalar : point.execution.roots.v3 = false
  plain : point.execution.roots.closed_form = false
  pending : point.execution.roots.pending = 0#usize
  direction : point.execution.roots.direction = 0#u32
  attempts : point.execution.roots.attempts = 0#usize
  hits : point.execution.hits.val = 0
  degree : point.execution.degree.val = support.card
  locator : slicePolynomial (prefixSlice point.workspace.bm (point.execution.degree.val + 1)) = supportLocator support
  workspace : WorkspaceAdmission.Admitted (workspaceLengths point.workspace)
    input.difference.length point.execution.budget.nonzero.val
  live : point.meter.exhausted = false

def ActualNativePlainCandidateFinishPositive : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    TimesXMod.ExactScaleXor kernels →
    (∀ (modulus table : Slice U64) (degree : Nat),
      CorrectTable modulus table degree → BackendSquareLaw kernels modulus table degree) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels → DirectTwo.CorrectArithmetic kernels →
    AffineEnumerate.HornerLaw kernels → ActualPaidVerificationAccepts kernels →
    ∀ (support : Finset Field) (input : RowInput) (before initial : RootDrainState K) (steps : Nat),
      let capacity := input.difference.length
      let budget := before.execution.budget.nonzero.val
      let beta := before.execution.budget.total
      0 < capacity → capacity ≤ 65535 → 0 < budget → budget ≤ capacity → beta.val ≤ 65535 →
      support.card ≤ budget → (0 : Field) ∉ support →
      (∀ i < capacity, toField input.difference[i]!.bv = oddSyndrome support i) →
      input.candidates.val = [] → PlainCandidate before input support →
      before.meter.used.val + plainCandidateWork capacity support.card beta ≤ before.meter.limit.val →
      SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
        steps initial before id →
      ∃ (sorted : Slice U64) (written : RowWorkspace) (paid : WorkMeter),
        let reply := if support.card = 0 ∧ beta = before.execution.budget.nonzero then RowResult.Equal
          else RowResult.Decoded sorted
        finish nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary kernels initial.execution
          input initial.workspace initial.meter = .ok (.Ok reply, written, id, paid) ∧
        rootSupport sorted = support ∧ sorted.val.Nodup ∧ sorted.length = support.card ∧
        sorted.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧
        written.roots.val.take support.card = sorted.val ∧ paid.limit = before.meter.limit ∧ paid.exhausted = false ∧
        paid.used.val ≤ before.meter.used.val + plainCandidateWork capacity support.card beta

theorem native_plain_candidate_finish_positive : ActualNativePlainCandidateFinishPositive := by
  intro K kernels scale backend raw square reduce mul inverse arithmetic horner accept
    support input before initial steps capacity budget beta positive capFit budgetPositive budgetCap betaFit
    supportFit nonzero syndromes noHints ready reserve segment
  let self := before.execution
  let workspace := before.workspace
  let meter := before.meter
  let degree := self.degree
  change meter.used.val + plainCandidateWork capacity support.card beta ≤ meter.limit.val at reserve
  have honest : degree.val = support.card := ready.degree
  let original := slicePolynomial (prefixSlice workspace.bm (degree.val + 1))
  have degreeFit : degree.val ≤ budget := ready.degree.trans_le supportFit
  have degreeMax : degree.val ≤ 65535 := degreeFit.trans (budgetCap.trans capFit)
  have locator : original = supportLocator support := ready.locator
  have monic : original.Monic := locator.symm ▸ supportLocator_monic support
  have exactDegree : original.natDegree = degree.val := by rw [locator, supportLocator_natDegree, ready.degree]
  have split : original.Splits := by
    rw [locator]
    apply Polynomial.Splits.prod
    intro root _
    exact Polynomial.Splits.X_sub_C root
  have supportRoots : (supportLocator support).roots = support.val := roots_prod_X_sub_C support
  have simple : original.roots.Nodup := by rw [locator, supportRoots]; exact support.nodup
  have nonzeroRoots : ∀ point, original.IsRoot point → point ≠ 0 := by
    intro point isRoot zero
    subst point
    have present := (mem_roots monic.ne_zero).mpr isRoot
    rw [locator, supportRoots] at present
    exact nonzero present
  have hintDistinct : input.candidates.val.Nodup := by simp [noHints]
  let charge := StageCharge.chargeResult meter (candidateCost degree input.candidates.len)
  have funded : meter.used.val ≤ meter.limit.val := by omega
  obtain ⟨paidCandidate, candidateUsed, candidateLimit, candidateLive⟩ :=
    no_hints_paid self input meter degreeMax noHints ready.live funded
  change charge.2.used = meter.used at candidateUsed
  change charge.2.limit = meter.limit at candidateLimit
  change charge.1 = .Ok () at paidCandidate
  have deflateRoom : charge.2.used.val + deflateUnits degree ≤ charge.2.limit.val := by
    rw [candidateUsed, candidateLimit]
    unfold plainCandidateWork at reserve
    have exact : deflateUnits degree = 2 * support.card * (support.card + 1) := by
      rw [deflateUnits, show degree.val = support.card from ready.degree]
    rw [exact]
    omega
  obtain ⟨paid, deflatePaid, deflateUsed, deflateLimit, deflateLive⟩ :=
    pay_checked charge.2 (deflateUnits degree) candidateLive deflateRoom
  obtain ⟨count, roots, values, final, candidateRan, deflateRan, _, represented, balance, _, emptied,
    sized, layout, mass, active, residualMonic, residualDegree, residualSplit, residualSimple, residualNonzero, _,
    admitted⟩ := native_candidate_deflate_driver_admitted nativeCanonicalize kernels horner mul self input workspace
      meter paid ready.state ready.noProbe ready.workspace budgetPositive budgetCap degreeFit ready.pending ready.hits
      hintDistinct monic exactDegree split simple nonzeroRoots paidCandidate deflatePaid
  change final.degree.val + count.val = degree.val at balance
  have finalBound : final.degree.val ≤ support.card := by omega
  let candidate := completedExecution self count false
  let next := { candidate with state := .Running .Deflation }
  let scanned := candidateWorkspace input workspace roots values
  let updated := finishedRoots next.roots final.degree
  let residual := activeLocator final.locator final.degree
  let joined := joinedWorkspace (deflateFrame next scanned (input.difference.length + 1)) final.locator final.quotient
  let written := RootSetup.startedWorkspace final.degree joined
  let beforeState := { next with roots := updated }
  let after : RootDrainState K := ⟨{ beforeState with state := .Running (ClosedLeafAdvance.stageFor updated) }, written, paid⟩
  have entered : RootTraversalInvariant (supportLocator support) updated written capacity budget := by
    rw [← locator]
    refine traversal_invariant_at_start original residual updated written capacity budget sized layout emptied ?_
      (mass.trans exactDegree.symm) (exactDegree.trans_le degreeFit) represented
      ⟨residualMonic, residualDegree, residualSplit, residualSimple, residualNonzero⟩ active
    change (ClosedLeafAdvance.usizeWord (final.degree.val + 1)).val = final.degree.val + 1
    have poly : 8 * (budget + 1) ≤ written.polynomials.length := sized.polynomials
    have max : written.polynomials.length ≤ Usize.max := written.polynomials.length_ineq
    have degreeBound : final.degree.val ≤ budget := finalBound.trans supportFit
    exact ClosedLeafAdvance.word_val _ (by omega)
  have emptyStack : updated.pending.val = 0 := by rw [emptied]; rfl
  have plain : updated.closed_form = false := ready.plain
  have scalar : updated.affine = false := by
    change (self.roots.v3 && decide (3 ≤ final.degree.val ∧ final.degree.val ≤ 18)) = false
    rw [show self.roots.v3 = false from ready.scalar]
    rfl
  have freshDirection : updated.direction.val = 0 := by
    change self.roots.direction.val = 0
    rw [show self.roots.direction = 0#u32 from ready.direction]
    rfl
  have freshAttempts : updated.attempts.val = 0 := by
    change self.roots.attempts.val = 0
    rw [show self.roots.attempts = 0#usize from ready.attempts]
    rfl
  have residualFit : updated.degree.val ≤ support.card := by
    change final.degree.val ≤ support.card
    exact finalBound
  have used : paid.used.val = meter.used.val + 2 * support.card * (support.card + 1) := by
    rw [deflateUsed, candidateUsed, deflateUnits, show degree.val = support.card from ready.degree]
  have limit : paid.limit = meter.limit := deflateLimit.trans candidateLimit
  have rootWork : frontierWork updated written.stack ≤ rootsEnvelope support.card := by
    change frontierCredits rootsEnvelope updated written.stack ≤ _
    unfold frontierCredits
    rw [emptyStack, Finset.range_zero, Finset.sum_empty, Nat.add_zero]
    exact rootsEnvelope_mono residualFit
  have nextReserve : paid.used.val + frontierWork updated written.stack +
      verificationReserve capacity support.card beta ≤ paid.limit.val := by
    rw [used, limit]
    unfold plainCandidateWork at reserve
    omega
  have admittedFrontier : NativeTraceFrontier (supportLocator support) after capacity budget := by
    refine ⟨rfl, ready.noProbe, entered, admitted, scalar, plain, ?_, ?_, ?_, ?_, deflateLive, ?_⟩
    · change TraceAgreement (activeFactor updated written) updated.splitter_seed updated.direction.val
      intro index lt
      omega
    · intro slot frame h
      change slot < updated.pending.val at h
      omega
    · intro basis exactBasis
      change none = some basis at exactBasis
      contradiction
    · change updated.attempts.val + 64 * frontierCredits (fun degree => degree - 1) updated written.stack ≤ Usize.max
      unfold frontierCredits
      rw [freshAttempts, emptyStack, Finset.range_zero, Finset.sum_empty, Nat.add_zero, Nat.zero_add]
      dsimp only
      have : 64 * (updated.degree.val - 1) ≤ 64 * 65535 :=
        Nat.mul_le_mul_left _ ((Nat.sub_le ..).trans (residualFit.trans (supportFit.trans (budgetCap.trans capFit))))
      have machine : 64 * 65535 ≤ Usize.max := by
        simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
        rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
      exact this.trans machine
    · change paid.used.val + frontierWork updated written.stack ≤ paid.limit.val
      omega
  let middle : RootDrainState K := ⟨next, scanned, charge.2⟩
  have chunk : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary kernels input
      2 before after id :=
    .step before middle after .CandidateEvaluation (progress .CandidateEvaluation candidate)
      id id 1 ready.state candidateRan
      (.step middle after after .Deflation (progress .Deflation beforeState) id id 0 rfl deflateRan (.empty after))
  have joinedChunk := append_successful_chunks segment chunk
  obtain ⟨sorted, out, resultMeter, result, supportEq, unique, length, order, pref, sameLimit, live, spent⟩ :=
    native_trace_recovered_after_prefix kernels scale backend raw square reduce mul inverse arithmetic accept
      support input after positive capFit budgetCap betaFit nonzero syndromes admittedFrontier nextReserve
      initial (steps + 2) joinedChunk
  refine ⟨sorted, out, resultMeter, result, supportEq, unique, length, order, pref, sameLimit.trans limit, live, ?_⟩
  change resultMeter.used.val ≤ paid.used.val + frontierWork updated written.stack +
      verificationReserve capacity support.card beta at spent
  rw [used] at spent
  change resultMeter.used.val ≤ meter.used.val + plainCandidateWork capacity support.card beta
  unfold plainCandidateWork
  omega

#print axioms native_plain_candidate_finish_positive

end BulksketchBridge.ExecutionDriver
