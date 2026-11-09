import BulksketchBridge.RootTraversalInvariant
import BulksketchBridge.RootNativeProperDivide

namespace BulksketchBridge.RootDivide

open Aeneas.Std RootRun Algebra.Gf64 Polynomial SliceKernels
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

theorem older_pending_factor (roots : Roots) (workspace written : RowWorkspace)
    (frame : FactorFrame) (slot : Nat) (live : slot < roots.pending.val)
    (shape : SlotLayout roots slot frame)
    (factorRoom : roots.pending.val * roots.stride.val ≤ workspace.factors.length)
    (sameWidth : written.factors.length = workspace.factors.length)
    (preserved : ∀ i < roots.pending.val * roots.stride.val, written.factors[i]! = workspace.factors[i]!) :
    pendingFactor written frame = pendingFactor workspace frame := by
  obtain ⟨start, _, length, _⟩ := shape
  let offset := frame.coefficient_start.val
  let stop := offset + frame.coefficient_len.val
  have ends : stop ≤ roots.pending.val * roots.stride.val := by
    unfold stop offset
    rw [start]
    calc
      _ ≤ slot * roots.stride.val + roots.stride.val := Nat.add_le_add_left length _
      _ = (slot + 1) * roots.stride.val := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have oldRoom : stop ≤ workspace.factors.length := ends.trans factorRoom
  have newRoom : stop ≤ written.factors.length := by rwa [sameWidth]
  unfold pendingFactor pendingCoefficients
  apply congrArg slicePolynomial
  have width := (ClosedLeaf.region_length written.factors offset stop newRoom).trans
    (ClosedLeaf.region_length workspace.factors offset stop oldRoom).symm
  apply Slice.ext_getElem width
  intro index newIndex oldIndex
  have within : index < stop - offset := by
    rwa [ClosedLeaf.region_length _ _ _ oldRoom] at oldIndex
  have inside : offset + index < roots.pending.val * roots.stride.val := by omega
  have word (words : Slice U64) (room : stop ≤ words.length) :
      (ClosedLeaf.region words offset stop)[index]! = words[offset + index]! := by
    simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice _ _ _ _ ⟨room, by omega⟩
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ newIndex, Slice.Inhabited_getElem_eq_getElem! _ _ oldIndex,
    word _ newRoom, word _ oldRoom, preserved _ inside]

/-- A paid original proper division preserves the whole live traversal
    invariant. It adds one valid pending factor and leaves the prepared
    affine table and its basis unchanged. -/
def ActualNativeProperDivideInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid finalMeter : WorkMeter) (capacity budget : Nat),
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels →
    RootTraversalInvariant locator roots workspace capacity budget →
    roots.direction.val + 1 ≤ U32.max →
    (roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64) →
    (roots.affine = true → ∃ directions, workspace.basis.directions = some directions) →
    StageCharge.chargeResult meter (divideCost roots.degree) = (.Ok (), paid) →
    StageCharge.chargeResult paid (assemblyCost roots.degree) = (.Ok (), finalMeter) →
    let buffers := buffersFor roots workspace
    let trace := slicePolynomial (DenseCoefficient.prefixSlice buffers.trace roots.trace_len.val)
    ProperGcdFrame roots buffers trace →
    ∃ after written,
      Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorDivision workspace meter =
        .ok (.Ok (.Ok (ClosedLeafAdvance.stageFor after)), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      traversalPotential after written.stack < traversalPotential roots workspace.stack ∧
      written.basis = workspace.basis ∧
      BmEntry.tail written.factors (after.stride.val * after.stride.val) =
        BmEntry.tail workspace.factors (roots.stride.val * roots.stride.val)

theorem native_proper_divide_invariant : ActualNativeProperDivideInvariant := by
  intro K kernels locator roots workspace meter paid finalMeter capacity budget mul raw reduce inverse
    invariant direction rank basis charged assembly buffers trace prior
  obtain ⟨sized, budgeted, layout, represented, exactMass, strideRoom, live, zeroActive, activeValid, pendingValid⟩ := invariant
  have positive : 0 < roots.degree.val := by have := prior.proper; omega
  have degreeRoom : roots.degree.val < roots.stride.val := by unfold liveDegree at live; omega
  have budgetMass : factorDegreeMass roots workspace.stack ≤ budget := exactMass.trans_le budgeted
  have positiveSlots := pending_degrees_positive locator roots workspace capacity budget
    ⟨sized, budgeted, layout, represented, exactMass, strideRoom, live, zeroActive, activeValid, pendingValid⟩
  obtain ⟨length, start, reply, after, written, ran, replyEq, startVal, rightPositive, afterDegree,
    _, _, pendingLayout, mass, decreases, product, widths, rootsFrame, basisFrame, tableFrame, sameCount,
    sameStride, pendingCount, earlierWords, earlierStack, frame, current, _, frameLength, both⟩ :=
    native_proper_divide kernels roots workspace meter paid finalMeter capacity budget mul raw reduce inverse
      sized strideRoom degreeRoom layout positiveSlots budgetMass direction rank basis charged assembly prior
  obtain ⟨leftValid, rightValid⟩ := both (activeValid positive)
  have afterPositive : 0 < after.degree.val := by rw [afterDegree]; exact prior.proper.1
  have exactProduct : activeTraversalProduct after written = locator := by
    have factor : activeTraversalProduct after written = activeTraversalProduct roots workspace := by
      unfold activeTraversalProduct traversalProduct
      simp only [Nat.ne_of_gt positive, Nat.ne_of_gt afterPositive, ite_false, Bool.false_eq_true]
      unfold emittedProduct
      rw [sameCount, rootsFrame, product]
    exact factor.trans represented
  have afterLive : liveDegree after written.stack < after.stride.val := by
    rw [sameStride]
    exact (live_degree_does_not_grow roots after workspace.stack written.stack mass (by rw [sameCount])).trans_lt live
  have sameFactors : written.factors.length = workspace.factors.length :=
    congrArg WorkspaceAdmission.Lengths.factors widths
  refine ⟨after, written, ?_, ?_, decreases, basisFrame, ?_⟩
  · rwa [replyEq] at ran
  · refine ⟨budget_buffers_same_lengths workspace written capacity budget sized widths, budgeted,
      pendingLayout, exactProduct, mass.trans exactMass, by rwa [sameStride], afterLive,
      (fun zero => (Nat.ne_of_gt afterPositive zero).elim), fun _ => leftValid, ?_⟩
    intro slot inStack
    by_cases older : slot < roots.pending.val
    · obtain ⟨oldFrame, oldRead, lengthPositive, oldValid⟩ := pendingValid slot older
      obtain ⟨layoutFrame, layoutRead, shape⟩ := layout.slots slot older
      have sameFrame := Option.some.inj (layoutRead.symm.trans oldRead)
      subst layoutFrame
      have sameFactor := older_pending_factor roots workspace written oldFrame slot older shape
        layout.factorRoom sameFactors (fun i bound => earlierWords i (startVal ▸ bound))
      refine ⟨oldFrame, ?_, lengthPositive, sameFactor.symm ▸ oldValid⟩
      rw [earlierStack slot older, oldRead]
    · have newest : slot = roots.pending.val := by omega
      subst slot
      exact ⟨frame, current, by omega, by rw [frameLength]; exact rightValid⟩
  · rw [sameStride]
    exact tableFrame live

#print axioms native_proper_divide_invariant

end BulksketchBridge.RootDivide
