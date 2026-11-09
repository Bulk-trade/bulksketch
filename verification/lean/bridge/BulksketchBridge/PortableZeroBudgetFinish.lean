import BulksketchBridge.PortableDecoderLaws
import BulksketchBridge.PortableCandidateWork
import BulksketchBridge.NativeDeflateTraversalEntry
import BulksketchBridge.CandidateHornerBridge

namespace BulksketchBridge.PortableDecoder

open Aeneas.Std Algebra.Gf64 Polynomial RootRun RootWorkBudget SliceKernels DenseCoefficient
open Reconciliation RebuiltLfsr CandidateOuter Deflation ExecutionDriver ExecutionDriverRuntime
open ExecutionFinish WorkSchedule
open bulksketch.backend.portable bulksketch.decode.roots bulksketch.decode.row bulksketch.decode.scratch
open bulksketch.decode.stages bulksketch.types
open bulksketch.decode.stages.Execution.Insts.BulksketchDecodeRowRowExecution (finish)
open AffineSelector (word word_val)

set_option maxRecDepth 4096
set_option maxHeartbeats 6000000

/-- With zero nonzero-ID budget the original Portable decoder performs
the admitted candidate, deflation and leaf steps without reading any
polynomial storage. Its full verifier still checks the empty support. -/
theorem zero_budget_finish (input : RowInput) (before initial : RootDrainState Portable)
    (steps : Nat)
    (running : before.execution.state = .Running .CandidateEvaluation)
    (noProbe : before.execution.degree_probe = none)
    (emptyStack : before.execution.roots.pending = 0#usize)
    (noHits : before.execution.hits.val = 0)
    (zeroBudget : before.execution.budget.nonzero.val = 0)
    (zeroDegree : before.execution.degree.val = 0)
    (oneLocator : slicePolynomial (prefixSlice before.workspace.bm
      (before.execution.degree.val + 1)) = (1 : Polynomial Field))
    (workspace : WorkspaceAdmission.Admitted (workspaceLengths before.workspace)
      input.difference.length before.execution.budget.nonzero.val)
    (capacityPositive : 0 < input.difference.length) (capacityFits : input.difference.length ≤ 65535)
    (betaFits : before.execution.budget.total.val ≤ 65535)
    (oddZero : ∀ i < input.difference.length, toField input.difference[i]!.bv = 0)
    (noHints : input.candidates.val = [])
    (live : before.meter.exhausted = false)
    (reserve : before.meter.used.val + verificationReserve input.difference.length 0
      before.execution.budget.total ≤ before.meter.limit.val)
    (prefixSteps : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary
      portableKernels input steps initial before id) :
    ∃ (sorted : Slice U64) (written : RowWorkspace) (paid : WorkMeter),
      let reply := if before.execution.budget.total = before.execution.budget.nonzero then RowResult.Equal
        else RowResult.Decoded sorted
      finish nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary portableKernels
        initial.execution input initial.workspace initial.meter = .ok (.Ok reply, written, id, paid) ∧
      rootSupport sorted = ∅ ∧ sorted.val.Nodup ∧ sorted.length = 0 ∧
      sorted.val.Pairwise Aeneas.Std.DegreeProbeRuntime.ordered ∧ written.roots.val.take 0 = sorted.val ∧
      paid.limit = before.meter.limit ∧ paid.exhausted = false ∧
      paid.used.val ≤ before.meter.used.val + verificationReserve input.difference.length 0
        before.execution.budget.total := by
  let self := before.execution
  let scratch := before.workspace
  let meter := before.meter
  let capacity := input.difference.length
  let beta := self.budget.total
  have inputCount : input.candidates.len.val = 0 := by simp [noHints]
  have deflateZero : deflateUnits self.degree = 0 := by change deflateUnits before.execution.degree = 0; simp [deflateUnits, zeroDegree]
  let charge := StageCharge.chargeResult meter (candidateCost self.degree input.candidates.len)
  obtain ⟨candidatePaid, deflateMeter, deflatePaid, deflateUsed, deflateLimit, deflateLive⟩ :=
    candidate_deflate_paid self.degree input.candidates.len meter (by change before.execution.degree.val ≤ _; omega)
      live (by rw [inputCount, deflateZero]; simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
               change meter.used.val + verificationReserve capacity 0 beta ≤ meter.limit.val at reserve
               omega)
  change charge.1 = .Ok () at candidatePaid
  change StageCharge.chargeResult charge.2 (deflateCost self.degree) = (.Ok (), deflateMeter) at deflatePaid
  have deflatedUsage : deflateMeter.used.val = meter.used.val := by
    rw [deflateUsed, inputCount, deflateZero]
    simp only [Nat.mul_zero, Nat.zero_mul, Nat.add_zero]
  let locator := slicePolynomial (prefixSlice scratch.bm (self.degree.val + 1))
  have locatorEq : locator = 1 := oneLocator
  have monic : locator.Monic := by rw [locatorEq]; exact monic_one
  have locatorDegree : locator.natDegree = self.degree.val := by rw [locatorEq, zeroDegree, natDegree_one]
  have split : locator.Splits := by rw [locatorEq]; exact Polynomial.Splits.one
  have simple : locator.roots.Nodup := by rw [locatorEq, roots_one]; exact Multiset.nodup_zero
  have nonzero : ∀ point, locator.IsRoot point → point ≠ 0 := by
    intro point root
    rw [locatorEq] at root
    simp [Polynomial.IsRoot] at root
  obtain ⟨count, roots, values, candidatesRan, handoff, _⟩ :=
    native_candidate_success_handoff portableKernels (candidate_horner_of_polynomial _ horner)
      self input scratch meter workspace (by rw [zeroBudget]; exact Nat.zero_le _)
      (by rw [zeroDegree, zeroBudget]) emptyStack noHits (by simp [noHints])
      monic locatorDegree split simple nonzero candidatePaid
  let candidate := completedExecution self count false
  let next := { candidate with state := .Running .Deflation }
  let scanned := candidateWorkspace input scratch roots values
  let middle : RootDrainState Portable := ⟨next, scanned, charge.2⟩
  have candidatesRan' : Execution.candidates RootSetup.gf64Dictionary portableKernels self input scratch meter =
      .ok (.Ok (.Ok (some .Deflation)), candidate, scanned, id, charge.2) := candidatesRan
  have runCandidate := run_next_return nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
    portableKernels self .CandidateEvaluation input scratch meter _ running
    (by rw [execute_refines nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
      portableKernels self .CandidateEvaluation input scratch meter, expectedExecute, noProbe]
        exact candidatesRan')
  have toDeflate : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary
      portableKernels input 1 before middle id :=
    SuccessfulChunk.step before middle middle .CandidateEvaluation (progress .CandidateEvaluation candidate)
      id id 0 running runCandidate (.empty middle)
  obtain ⟨budgetCap, degreeBound, hitBound, exactCount, emptyPending, writtenAdmitted⟩ := handoff
  have nextHandoff : DeflateCandidateHandoff next input scanned :=
    ⟨budgetCap, degreeBound, hitBound, exactCount, emptyPending, writtenAdmitted⟩
  have nextDegree : next.degree = self.degree := rfl
  have nextProbe : next.degree_probe = none := noProbe
  obtain ⟨_, _, ranDeflate, _, rootPending, rootCount, rootDegree, _, admitted⟩ :=
    native_deflate_zero_budget RootSetup.gf64Dictionary portableKernels mul_word next input scanned charge.2
      deflateMeter nextHandoff zeroBudget (by rwa [nextDegree])
  let updated := finishedRoots next.roots 0#usize
  let written := { scanned with basis := ⟨none, 0#u32⟩ }
  let deflated := { next with roots := updated }
  let leaf : RootDrainState Portable := ⟨{ deflated with state := .Running .Leaf }, written, deflateMeter⟩
  have runDeflate := run_next_return nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
    portableKernels next .Deflation input scanned charge.2 _ rfl
    (by rw [execute_refines nativeCalls nativeDivRem nativeCanonicalize RootSetup.gf64Dictionary
      portableKernels next .Deflation input scanned charge.2, expectedExecute, nextProbe]
        exact ranDeflate)
  have toLeaf : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary
      portableKernels input 1 middle leaf id :=
    SuccessfulChunk.step middle leaf leaf .Deflation (progress .Deflation deflated)
      id id 0 rfl runDeflate (.empty leaf)
  have leafPrice : bulksketch.decode.work.WorkScheduleV1.cost (.Leaf updated.degree) =
      .ok (.Ok 0#u64) := by rw [rootDegree]; rfl
  have deflatedRoom : deflateMeter.used.val ≤ deflateMeter.limit.val := by
    rw [deflatedUsage, deflateLimit]
    change meter.used.val + verificationReserve capacity 0 beta ≤ meter.limit.val at reserve
    omega
  obtain ⟨leafMeter, leafPaid, leafUsed, leafLimit, leafLive⟩ :=
    native_roots_paid_charge deflateMeter (.Leaf updated.degree) 0#u64 0 leafPrice rfl deflateLive
      (by simpa only [Nat.add_zero] using deflatedRoom)
  have leafRan := RootLeaf.native_empty_leaf portableKernels updated written deflateMeter leafMeter direct_two
    rootDegree rootPending (by rw [rootCount]; exact Nat.zero_le _) leafPaid
  let verified : RootDrainState Portable := advanceRootState leaf .Verification updated written leafMeter
  have runLeaf := native_root_driver_return nativeCanonicalize portableKernels leaf.execution .Leaf input
    written deflateMeter leafMeter (.Ok (.Ok .Verification)) updated written id rfl noProbe rfl leafRan
  have toVerify : SuccessfulChunk (nativeDrainRuntime nativeCanonicalize) RootSetup.gf64Dictionary
      portableKernels input 1 leaf verified id :=
    SuccessfulChunk.step leaf verified verified .Leaf (progress .Leaf leaf.execution)
      id id 0 rfl runLeaf (.empty verified)
  have allSteps := append_successful_chunks
    (append_successful_chunks (append_successful_chunks prefixSteps toDeflate) toLeaf) toVerify
  simp only [Function.id_comp] at allSteps
  have capWord : input.difference.len.val = capacity := Slice.len_val ..
  obtain ⟨full, rebuilt, fullFit, rebuiltFit⟩ := native_v3_verifier_quotes input.difference.len
    verified.execution.roots.count beta (capWord.symm ▸ capacityFits)
    (by change updated.count.val ≤ 65535; rw [rootCount]; decide) betaFits
  have countZero : verified.execution.roots.count.val = 0 := by
    change updated.count.val = 0
    rw [rootCount]
    rfl
  rw [capWord, countZero] at rebuilt rebuiltFit
  rw [capWord] at full fullFit
  have price : ∃ amount, ExecutionVerify.actualCost verified.execution input = .Ok amount ∧
      amount.val ≤ max (originalVerifyUnits capacity beta.val) (rebuiltVerifyUnits capacity 0 beta.val) := by
    have actual := ExecutionVerify.actual_cost_refines verified.execution input
    unfold ExecutionVerify.priceTag at actual
    have betaEq : verified.execution.budget.total = beta := rfl
    rw [betaEq] at actual
    cases selected : ExecutionVerify.selects verified.execution input
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
  have leafUsage : leafMeter.used.val = meter.used.val := by rw [leafUsed, deflatedUsage, Nat.add_zero]
  have leafLimitEq : leafMeter.limit = meter.limit := leafLimit.trans deflateLimit
  have remaining : leafMeter.used.val + amount.val + CanonicalizePrice.units beta ≤ leafMeter.limit.val := by
    rw [leafUsage, leafLimitEq]
    change meter.used.val + verificationReserve capacity 0 beta ≤ meter.limit.val at reserve
    unfold verificationReserve at reserve
    omega
  have amountFits : amount.val ≤ U64.max := by simpa only [U64.max_eq] using amount.le_max
  have checkedAmount : checkedCost amount.val = .Ok amount :=
    (checked_cost_ok_iff _ _).mpr ⟨amountFits, rfl⟩
  obtain ⟨first, firstCharge, firstUsed, firstLimit, firstLive⟩ :=
    charge_checked leafMeter amount.val leafLive (by omega)
  obtain ⟨paid, finalCharge, paidUsed, paidLimit, paidLive⟩ :=
    charge_checked first (CanonicalizePrice.units beta) firstLive (by rw [firstUsed, firstLimit]; exact remaining)
  have represented : emittedProduct verified.execution.roots verified.workspace =
      supportLocator (∅ : Finset Field) := by
    simp [emittedProduct, countZero, rootsProduct, supportLocator]
  have exactOdd : ∀ i < input.difference.length,
      toField input.difference[i]!.bv = oddSyndrome (∅ : Finset Field) i := by
    intro i inside
    simpa only [oddSyndrome, powerSum, Finset.sum_empty] using oddZero i inside
  have ready : WorkspaceAdmission.Admitted (workspaceLengths verified.workspace) input.difference.length
      verified.execution.budget.nonzero.val := by
    change WorkspaceAdmission.Admitted (workspaceLengths written) input.difference.length self.budget.nonzero.val
    rwa [zeroBudget]
  have firstPaid : StageCharge.chargeResult verified.meter (ExecutionVerify.actualCost verified.execution input) =
      (.Ok (), first) := by rw [exactPrice]; rwa [checkedAmount] at firstCharge
  have finalPaid : canonicalStageCharge verified.execution first = (.Ok (), paid) := finalCharge
  obtain ⟨finalWorkspace, result, sameSupport, distinct, length, ordered, writtenPrefix⟩ :=
    native_recovered_support_after_chunk portableKernels paid_verification verified input ∅ first paid
      rfl noProbe ready capacityPositive (by change self.budget.nonzero.val ≤ _; rw [zeroBudget]; exact Nat.zero_le _)
      (by change updated.count.val ≤ self.budget.nonzero.val
          rw [rootCount]
          exact Nat.zero_le _)
      (by simp) represented exactOdd firstPaid finalPaid initial _ allSteps
  refine ⟨_, finalWorkspace, paid, ?_, sameSupport, distinct, ?_, ordered, ?_, ?_, paidLive, ?_⟩
  · have emptyCount : verified.execution.roots.count = 0#usize := rootCount
    have budgetEq : verified.execution.budget = before.execution.budget := rfl
    simpa only [emptyCount, true_and, eq_self, budgetEq] using result
  · simpa only [Finset.card_empty] using length
  · simpa only [countZero] using writtenPrefix
  · exact paidLimit.trans (firstLimit.trans leafLimitEq)
  · rw [paidUsed, firstUsed, leafUsage]
    change meter.used.val + amount.val + CanonicalizePrice.units beta ≤
      meter.used.val + verificationReserve capacity 0 beta
    unfold verificationReserve
    omega

end BulksketchBridge.PortableDecoder
