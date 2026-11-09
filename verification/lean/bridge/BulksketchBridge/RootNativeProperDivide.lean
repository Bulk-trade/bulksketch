import BulksketchBridge.RootDivideArena
import BulksketchBridge.RootDivideCommitDegree
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootPendingProduct
import BulksketchBridge.RootFactorValidity
import BulksketchBridge.RootAffineTableFrame

namespace BulksketchBridge.RootDivide

open Aeneas Aeneas.Std RootRun DenseCoefficient RebuiltLfsr BmEntry SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem rebuilt_modulus_prefix (roots : Roots) (workspace : RowWorkspace) (buffers : FactorWork)
    (fits : roots.degree.val + 1 ≤ workspace.polynomials.length)
    (width : buffers.modulus.length = roots.degree.val + 1)
    (count : Nat) (countBound : count ≤ roots.degree.val + 1) :
    prefixSlice (rebuild workspace roots buffers).polynomials count = prefixSlice buffers.modulus count := by
  let width := roots.degree.val + 1
  let afterModulus := tail workspace.polynomials width
  let afterTrace := tail afterModulus roots.degree.val
  let rest := splitBack afterModulus roots.degree.val
    (buffers.trace, splitBack afterTrace width (buffers.gcd, buffers.work))
  have restWidth : rest.length = workspace.polynomials.length - width :=
    (splitBack_length ..).trans (tail_length ..)
  have lengths : buffers.modulus.length = min width workspace.polynomials.length ∧
      rest.length = workspace.polynomials.length - width :=
    ⟨by rw [Nat.min_eq_left fits]; exact ‹buffers.modulus.length = roots.degree.val + 1›, restWidth⟩
  change prefixSlice (splitBack workspace.polynomials width (buffers.modulus, rest)) count = _
  apply Slice.ext
  rw [splitBack, dite_eq_left lengths]
  simp only [prefixSlice, Slice.from_val]
  have fitsPrefix : count ≤ buffers.modulus.val.length := by
    change count ≤ buffers.modulus.length
    omega
  exact List.take_append_of_le_length fitsPrefix

/-- Exact FactorDivision dispatch after both work charges. Native GCD
divisibility, the live budget and pending layout supply the callee and
offset admission. The frame preserves degree mass and strictly lowers the
sum of squared live factor degrees. -/
def ActualNativeProperDivide : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid finalMeter : WorkMeter)
    (capacity budget : Nat),
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels →
    BudgetBuffers workspace capacity budget →
    roots.stride.val ≤ budget + 1 → roots.degree.val < roots.stride.val →
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    (∀ slot < roots.pending.val, 0 < slotDegree workspace.stack slot) →
    factorDegreeMass roots workspace.stack ≤ budget →
    roots.direction.val + 1 ≤ U32.max →
    (roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64) →
    (roots.affine = true → ∃ directions, workspace.basis.directions = some directions) →
    StageCharge.chargeResult meter (divideCost roots.degree) = (.Ok (), paid) →
    StageCharge.chargeResult paid (assemblyCost roots.degree) = (.Ok (), finalMeter) →
    let buffers := buffersFor roots workspace
    let trace := slicePolynomial (prefixSlice buffers.trace roots.trace_len.val)
    ProperGcdFrame roots buffers trace →
    ∃ (length start : Usize) (reply : Reply) (after : Roots) (written : RowWorkspace),
      Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorDivision workspace meter =
        .ok (reply, after, written, id, finalMeter) ∧
      reply = .Ok (.Ok (ClosedLeafAdvance.stageFor after)) ∧
      start.val = roots.pending.val * roots.stride.val ∧
      0 < length.val - 1 ∧ after.degree = roots.gcd_degree ∧
      activeFactor after written = gcd (activeFactor roots workspace) trace ∧
      activeFactor roots workspace =
        slicePolynomial (ClosedLeaf.region written.factors start.val (start.val + length.val)) *
          activeFactor after written ∧
      PendingLayout after written.stack written.factors.length written.polynomials.length ∧
      factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack ∧
      traversalPotential after written.stack < traversalPotential roots workspace.stack ∧
      liveProduct after written = liveProduct roots workspace ∧
      workspaceLengths written = workspaceLengths workspace ∧
      written.roots = workspace.roots ∧ written.basis = workspace.basis ∧
      (liveDegree roots workspace.stack < roots.stride.val →
        tail written.factors (roots.stride.val * roots.stride.val) =
          tail workspace.factors (roots.stride.val * roots.stride.val)) ∧
      after.count = roots.count ∧ after.stride = roots.stride ∧ after.pending.val = roots.pending.val + 1 ∧
      (∀ index < start.val, written.factors[index]! = workspace.factors[index]!) ∧
      (∀ slot < roots.pending.val, written.stack.val[slot]? = workspace.stack.val[slot]?) ∧
      ∃ frame, written.stack.val[roots.pending.val]? = some frame ∧
        frame.coefficient_start.val = start.val ∧ frame.coefficient_len.val = length.val ∧
        (ValidFactor (activeFactor roots workspace) roots.degree.val →
          ValidFactor (activeFactor after written) after.degree.val ∧
          ValidFactor (pendingFactor written frame) (length.val - 1))

set_option maxHeartbeats 4400000 in
theorem native_proper_divide : ActualNativeProperDivide := by
  intro K kernels roots workspace meter paid finalMeter capacity budget mul rawLaw reduce inverse
    sized strideBound activeWidth layout positiveSlots mass direction rank basis charged assembly buffers trace prior
  have degreeBound : roots.degree.val ≤ budget := by unfold factorDegreeMass at mass; omega
  have degreeMin : 2 ≤ roots.degree.val := by have := prior.proper; omega
  have factorReady := (gcd_buffers_of_budget roots workspace capacity budget sized degreeMin degreeBound).1
  obtain ⟨ready, shape⟩ := divide_ready_of_budget roots workspace capacity budget trace sized degreeBound prior
  change NativeDivideReady roots buffers at ready
  change ProperDivideShape roots buffers at shape
  obtain ⟨length, candidate, positive, quotientFits, _, degrees, product⟩ :=
    native_proper_gcd_has_quotient roots buffers trace ready shape prior.gcdExact
  obtain ⟨start, stop, startOk, endOk, startVal, lengthRoom, slotEnd, commit⟩ :=
    divide_commit_of_budget roots workspace capacity budget buffers length sized strideBound activeWidth
      positiveSlots mass direction rank basis ready shape candidate
  let call := nativeCall roots buffers
  let output := committed roots buffers workspace.factors workspace.stack finalMeter length start call.2.1 call.2.2.1 call.2.2.2
  let written := { rebuild workspace roots output.2.2.1 with factors := output.2.2.2.2.1, stack := output.2.2.2.2.2.1 }
  have nativeLaw := DenseDivRem.actual_native_div_rem kernels mul rawLaw reduce inverse
  obtain ⟨ran, massEq, _⟩ := native_committed_degree_mass nativeDivRem kernels roots buffers workspace.factors workspace.stack
    meter paid finalMeter length start stop nativeLaw ready shape candidate charged assembly startOk endOk commit
  have exactStage : Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorDivision workspace meter =
      .ok (output.1, output.2.1, written, id, finalMeter) := by
    rw [original_root_run_refines kernels roots .FactorDivision workspace meter factorReady]
    unfold RootRun.expected
    rw [ran]
    simp only [bind_ok]
    rfl
  have newSlotEnd : start.val + roots.stride.val ≤ workspace.factors.length := by
    rwa [Nat.add_mul, Nat.one_mul, ← startVal] at slotEnd
  obtain ⟨leftWords, rightWords⟩ := committed_coefficients roots buffers workspace.factors workspace.stack finalMeter
    length start call.2.1 call.2.2.1 call.2.2.2 (by omega) quotientFits lengthRoom.le newSlotEnd
    (fun _ => lengthRoom) ready.gcdRoom commit.modulusRoom
  have afterDegree : output.2.1.degree = roots.gcd_degree := rfl
  have leftWidth : output.2.1.degree.val + 1 = roots.gcd_len.val := by rw [afterDegree, shape.gcdWidth]
  have modulusWidth : output.2.2.1.modulus.length = roots.degree.val + 1 := by
    change (restorePrefix buffers.modulus (prefixSlice buffers.gcd roots.gcd_len.val)).length = _
    rw [restore_length, shape.modulusWidth]
  have polyFits : roots.degree.val + 1 ≤ workspace.polynomials.length := by have := factorReady.1; omega
  have active : activeFactor output.2.1 written = slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) := by
    unfold activeFactor
    rw [leftWidth]
    change slicePolynomial (prefixSlice (rebuild workspace roots output.2.2.1).polynomials roots.gcd_len.val) = _
    rw [rebuilt_modulus_prefix roots workspace output.2.2.1 polyFits modulusWidth _ (by
      have bound := shape.proper
      rw [shape.gcdWidth]
      omega), leftWords]
  have parent : activeFactor roots workspace = slicePolynomial buffers.modulus := rfl
  have right : ClosedLeaf.region written.factors start.val (start.val + length.val) = prefixSlice call.2.1 length.val :=
    rightWords
  have polyLen : written.polynomials.length = workspace.polynomials.length := by
    simp only [written, rebuild, RootSetup.restoreWork, splitBack_length]
  have stackRoom : roots.pending.val + 1 ≤ workspace.stack.length := by have := commit.slotRoom; omega
  obtain ⟨layoutAfter, preserved⟩ := commit_with_pending_layout roots buffers workspace.factors workspace.stack
    finalMeter length start call.2.1 call.2.2.1 call.2.2.2 workspace.polynomials.length layout stackRoom
    slotEnd startVal (by omega) lengthRoom.le (fun _ => lengthRoom)
  have decreases := committed_potential_decreases roots buffers workspace.factors workspace.stack finalMeter
    length start call.2.1 call.2.2.1 call.2.2.2 commit.slotRoom degrees shape.gcdPositive positive
  obtain ⟨pending, pendingCount, factorWidth, stackWidth, earlierStack, frame, frameRead, frameStart, frameLength⟩ :=
    committed_pending_product roots workspace buffers finalMeter length start call.2.1 call.2.2.1 call.2.2.2
      layout stackRoom slotEnd startVal (by omega) lengthRoom quotientFits ready.gcdRoom commit.modulusRoom
  change pendingProduct written output.2.1.pending.val =
    pendingProduct workspace roots.pending.val * slicePolynomial (prefixSlice call.2.1 length.val) at pending
  have sameProduct : liveProduct output.2.1 written = liveProduct roots workspace := by
    unfold liveProduct
    rw [active, pending, parent, product]
    ring
  have rawWidth : output.2.2.1.raw.length = workspace.raw.length :=
    native_call_raw_width roots buffers
  have lengths : workspaceLengths written = workspaceLengths workspace := by
    change workspaceLengths
      { rebuild workspace roots output.2.2.1 with factors := output.2.2.2.2.1, stack := output.2.2.2.2.2.1 } = _
    change output.2.2.2.2.1.length = workspace.factors.length at factorWidth
    change output.2.2.2.2.2.1.length = workspace.stack.length at stackWidth
    simp only [workspaceLengths, rebuild, RootSetup.restoreWork, splitBack_length, restore_length,
      factorWidth, stackWidth, rawWidth]
  have current : written.stack.val[roots.pending.val]? = some frame := frameRead
  have pendingFactorEq : pendingFactor written frame = slicePolynomial (prefixSlice call.2.1 length.val) := by
    unfold pendingFactor pendingCoefficients
    rw [frameStart, frameLength, right]
  have children (valid : ValidFactor (activeFactor roots workspace) roots.degree.val) :
      ValidFactor (activeFactor output.2.1 written) output.2.1.degree.val ∧
      ValidFactor (pendingFactor written frame) (length.val - 1) := by
    have nozero : gcd (slicePolynomial buffers.modulus) trace ≠ 0 :=
      fun zero => prior.monic.ne_zero ((gcd_eq_zero_iff _ _).mp zero).1
    have gcdMonic := (normalize_eq_self_iff_monic nozero).mp (normalize_gcd (slicePolynomial buffers.modulus) trace)
    have activeGcd : activeFactor output.2.1 written = gcd (slicePolynomial buffers.modulus) trace :=
      active.trans prior.gcdExact
    have activeMonic : (activeFactor output.2.1 written).Monic := activeGcd.symm ▸ gcdMonic
    have exactDegree : (activeFactor output.2.1 written).natDegree = output.2.1.degree.val :=
      (congrArg Polynomial.natDegree activeGcd).trans
        (prior.gcdDegree.symm.trans (congrArg UScalar.val afterDegree.symm))
    have childProduct : activeFactor roots workspace =
        pendingFactor written frame * activeFactor output.2.1 written :=
      parent.trans (product.trans (congrArg₂ (· * ·) pendingFactorEq.symm active.symm))
    have childSum : output.2.1.degree.val + (length.val - 1) = roots.degree.val :=
      (congrArg (fun d : Usize => d.val + (length.val - 1)) afterDegree).trans degrees
    exact valid_children (activeFactor roots workspace) (activeFactor output.2.1 written)
      (pendingFactor written frame) roots.degree.val output.2.1.degree.val (length.val - 1)
      valid childProduct activeMonic exactDegree childSum
  have tableFrame (live : liveDegree roots workspace.stack < roots.stride.val) :
      tail written.factors (roots.stride.val * roots.stride.val) =
        tail workspace.factors (roots.stride.val * roots.stride.val) := by
    have before := next_slot_before_affine_table roots workspace.stack positiveSlots (by omega) live
    rw [← startVal] at before
    exact committed_preserves_affine_table roots buffers workspace.factors call.2.1 call.2.2.1
      workspace.stack finalMeter length start call.2.2.2 (by omega) lengthRoom.le newSlotEnd before
  refine ⟨length, start, output.1, output.2.1, written, exactStage, rfl, startVal, positive, afterDegree,
    ?_, ?_, ?_, massEq, decreases, sameProduct, lengths, rfl, rfl, tableFrame, rfl, rfl, pendingCount, preserved, earlierStack,
    frame, current, frameStart, frameLength, children⟩
  · rw [active, parent]
    exact prior.gcdExact
  · rw [parent, active, right]
    exact product
  · rwa [polyLen]

#print axioms native_proper_divide

end BulksketchBridge.RootDivide
