import BulksketchBridge.RootDivideInvariant
import BulksketchBridge.RootTraceProgress
import BulksketchBridge.RootTraversalRanking
import BulksketchBridge.RootTraversalFactor

namespace BulksketchBridge.RootDivide

open Aeneas Aeneas.Std RootRun RootTrace DenseCoefficient BmEntry SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 5200000

/-- The original proper divide transfers trace agreement to both live
    children at the exact incremented direction, including the saved
    resume direction and checked bit of the pending frame. -/
def ActualNativeTraceDivideHandoff : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid finalMeter : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → roots.affine = false →
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels →
    StageCharge.chargeResult meter (divideCost roots.degree) = (.Ok (), paid) →
    StageCharge.chargeResult paid (assemblyCost roots.degree) = (.Ok (), finalMeter) →
    let buffers := buffersFor roots workspace
    let trace := slicePolynomial (prefixSlice buffers.trace roots.trace_len.val)
    ProperGcdFrame roots buffers trace →
    TraceAgreement (activeFactor roots workspace) roots.splitter_seed roots.direction.val →
    (∀ point, (activeFactor roots workspace).IsRoot point →
      (trace.IsRoot point ↔ traceBit roots.splitter_seed roots.direction.val point = 0)) →
    ∃ (after : Roots) (written : RowWorkspace) (frame : FactorFrame),
      Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorDivision workspace meter =
        .ok (.Ok (.Ok (ClosedLeafAdvance.stageFor after)), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      traversalRank (ClosedLeafAdvance.stageFor after) after written < traversalRank .FactorDivision roots workspace ∧
      after.affine = false ∧ after.checked = true ∧ after.splitter_seed = roots.splitter_seed ∧
      after.direction.val = roots.direction.val + 1 ∧
      written.basis = workspace.basis ∧
      written.stack.val[roots.pending.val]? = some frame ∧
      frame.next_direction = after.direction ∧ frame.split_checked = 1#u32 ∧
      (∀ i < frame.coefficient_start.val, written.factors[i]! = workspace.factors[i]!) ∧
      (∀ slot < roots.pending.val, written.stack.val[slot]? = workspace.stack.val[slot]?) ∧
      TraceAgreement (activeFactor after written) after.splitter_seed after.direction.val ∧
      TraceAgreement (pendingFactor written frame) after.splitter_seed frame.next_direction.val

theorem native_trace_divide_handoff : ActualNativeTraceDivideHandoff := by
  intro K kernels locator roots workspace meter paid finalMeter capacity budget invariant affine
    mul raw reduce inverse charged assembly buffers trace prior agrees classifies
  have degreeBound := traversal_degree_budget locator roots workspace capacity budget invariant
  have degreeMin : 2 ≤ roots.degree.val := by have := prior.proper; omega
  have positive : 0 < roots.degree.val := by omega
  have valid := invariant.active positive
  have directionFits := trace_agreement_before_end (activeFactor roots workspace) roots.splitter_seed
    roots.direction.val valid.monic.ne_zero valid.split valid.simple (by rw [valid.exactDegree]; omega) agrees
  have direction : roots.direction.val + 1 ≤ U32.max := by rw [U32.max_eq]; omega
  have degreeRoom : roots.degree.val < roots.stride.val := by have := invariant.live; unfold liveDegree at this; omega
  have mass : factorDegreeMass roots workspace.stack ≤ budget := invariant.mass.trans_le invariant.degreeBudget
  have positiveSlots := pending_degrees_positive locator roots workspace capacity budget invariant
  have rankRoom : roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64 := by simp [affine]
  have basisRoom : roots.affine = true → ∃ directions, buffers.basis.directions = some directions := by simp [affine]
  obtain ⟨length, start, reply, after, written, ran, replyEq, _, _, _, activeGcd,
    product, _, _, _, _, _, _, basisFrame, _, _, _, _, earlierWords, earlierStack, frame,
    frameRead, frameStart, frameLength, _⟩ :=
    native_proper_divide kernels roots workspace meter paid finalMeter capacity budget mul raw reduce inverse
      invariant.buffers invariant.stride degreeRoom invariant.layout positiveSlots mass direction rankRoom
      basisRoom charged assembly prior
  obtain ⟨invariantAfter, invariantWritten, ranInvariant, preserved, smaller, _, _⟩ :=
    native_proper_divide_invariant kernels locator roots workspace meter paid finalMeter capacity budget
      mul raw reduce inverse invariant direction rankRoom basisRoom charged assembly prior
  rw [replyEq] at ran
  have exactInvariant := Result.ok_injective (ranInvariant.symm.trans ran)
  have afterEq : invariantAfter = after := congrArg (fun result : RootRun.Frame => result.2.1) exactInvariant
  have writtenEq : invariantWritten = written := congrArg (fun result : RootRun.Frame => result.2.2.1) exactInvariant
  subst invariantAfter invariantWritten
  obtain ⟨ready, shape⟩ := divide_ready_of_budget roots workspace capacity budget trace invariant.buffers degreeBound prior
  obtain ⟨len, candidate, _, _, _, _, _⟩ :=
    native_proper_gcd_has_quotient roots buffers trace ready shape prior.gcdExact
  obtain ⟨offset, stop, startOk, endOk, _, _, _, commit⟩ :=
    divide_commit_of_budget roots workspace capacity budget buffers len invariant.buffers invariant.stride
      degreeRoom positiveSlots mass direction rankRoom basisRoom ready shape candidate
  let call := nativeCall roots buffers
  let output := committed roots buffers workspace.factors workspace.stack finalMeter len offset call.2.1 call.2.2.1 call.2.2.2
  let modelWritten := { rebuild workspace roots output.2.2.1 with factors := output.2.2.2.2.1, stack := output.2.2.2.2.2.1 }
  have law := DenseDivRem.actual_native_div_rem kernels mul raw reduce inverse
  obtain ⟨ranDivide, _, _⟩ := native_committed_degree_mass nativeDivRem kernels roots buffers workspace.factors workspace.stack
    meter paid finalMeter len offset stop law ready shape candidate charged assembly startOk endOk commit
  have ranModel : Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorDivision workspace meter =
      .ok (output.1, output.2.1, modelWritten, id, finalMeter) := by
    rw [original_root_run_refines kernels roots .FactorDivision workspace meter
      (gcd_buffers_of_budget roots workspace capacity budget invariant.buffers degreeMin degreeBound).1]
    unfold RootRun.expected
    rw [ranDivide]
    simp only [bind_ok]
    rfl
  have modelEq := Result.ok_injective (ranModel.symm.trans ran)
  have actualRoots : output.2.1 = after := congrArg (fun result : RootRun.Frame => result.2.1) modelEq
  have actualWorkspace : modelWritten = written := congrArg (fun result : RootRun.Frame => result.2.2.1) modelEq
  let saved : FactorFrame := ⟨UScalar.cast .U64 offset, UScalar.cast .U64 len, directionWord roots, 1#u32⟩
  have readSaved : modelWritten.stack.val[roots.pending.val]? = some saved := by
    simp only [modelWritten, output, committed, affine, Bool.false_eq_true, ite_false, Slice.set_val_eq]
    exact List.getElem?_set_self commit.slotRoom
  rw [actualWorkspace, frameRead] at readSaved
  have frameEq := Option.some.inj readSaved
  have sameAffine : after.affine = false := by
    rw [← actualRoots]
    simp only [output, committed, affine, Bool.false_eq_true, ite_false]
  have sameChecked : after.checked = true := by
    rw [← actualRoots]
    simp only [output, committed, affine, Bool.false_eq_true, ite_false]
  have sameSeed : after.splitter_seed = roots.splitter_seed := by
    rw [← actualRoots]
    simp only [output, committed, affine, Bool.false_eq_true, ite_false]
  have nextDirection : after.direction = directionWord roots := by
    rw [← actualRoots]
    simp only [output, committed, affine, Bool.false_eq_true, ite_false]
  have nextVal : after.direction.val = roots.direction.val + 1 := by
    rw [nextDirection]
    change (BitVec.ofNat 32 (roots.direction.val + 1)).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have savedDirection : frame.next_direction = after.direction := by rw [frameEq, nextDirection]
  have savedChecked : frame.split_checked = 1#u32 := frameEq.symm ▸ rfl
  have rightProduct : activeFactor roots workspace = pendingFactor written frame * activeFactor after written := by
    unfold pendingFactor pendingCoefficients
    rw [frameStart, frameLength]
    exact product
  have squarefree : Squarefree (activeFactor roots workspace) :=
    ((nodup_roots_iff_of_splits valid.monic.ne_zero valid.split).mp valid.simple).squarefree
  obtain ⟨leftAgreement, rightAgreement⟩ :=
    trace_agreement_after_division (activeFactor roots workspace) trace (activeFactor after written)
      (pendingFactor written frame) roots.splitter_seed roots.direction.val squarefree activeGcd rightProduct agrees classifies
  refine ⟨after, written, frame, ran, preserved, traversal_rank_decreases _ _ _ _ _ _ (Or.inl smaller),
    sameAffine, sameChecked, sameSeed, nextVal, basisFrame, frameRead, savedDirection, savedChecked,
    ?_, earlierStack, ?_, ?_⟩
  · rw [frameStart]
    exact earlierWords
  · simpa only [sameSeed, nextVal] using leftAgreement
  · simpa only [sameSeed, savedDirection, nextVal] using rightAgreement

#print axioms native_trace_divide_handoff

end BulksketchBridge.RootDivide
