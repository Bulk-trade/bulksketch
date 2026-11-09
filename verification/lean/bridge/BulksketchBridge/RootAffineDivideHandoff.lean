import BulksketchBridge.RootDivideInvariant
import BulksketchBridge.RootAffineChildren
import BulksketchBridge.RootTraversalRanking
import BulksketchBridge.RootTraversalFactor

namespace BulksketchBridge.RootDivide

open Aeneas Aeneas.Std RootRun DenseCoefficient BmEntry SliceKernels Algebra.Gf64 Polynomial
open AffineSubspaces AffineSubspaceAlgebra
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 5200000

/-- The exact original paid divide reaches the next root stage with its
    active child and pending child in the selected affine half-cosets. -/
def ActualNativeAffineDivideHandoff : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid finalMeter : WorkMeter) (capacity budget : Nat) (basis : Array U64 64#usize),
    RootTraversalInvariant locator roots workspace capacity budget →
    roots.affine = true → roots.affine_ready = true →
    0 < roots.affine_rank.val → roots.affine_rank.val ≤ 64 →
    roots.direction.val + 1 ≤ U32.max → workspace.basis.directions = some basis →
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels →
    StageCharge.chargeResult meter (divideCost roots.degree) = (.Ok (), paid) →
    StageCharge.chargeResult paid (assemblyCost roots.degree) = (.Ok (), finalMeter) →
    let buffers := buffersFor roots workspace
    let trace := slicePolynomial (prefixSlice buffers.trace roots.trace_len.val)
    let rank := roots.affine_rank.val - 1
    ProperGcdFrame roots buffers trace →
    AffineSplitClassifier (activeFactor roots workspace) trace roots.affine_base basis[rank]!
      basis.to_slice rank →
    ∃ (after : Roots) (written : RowWorkspace) (frame : FactorFrame),
      Roots.run nativeCalls nativeDivRem RootRun.dictionary kernels roots .FactorDivision workspace meter =
        .ok (.Ok (.Ok (ClosedLeafAdvance.stageFor after)), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      traversalRank (ClosedLeafAdvance.stageFor after) after written < traversalRank .FactorDivision roots workspace ∧
      after.affine = true ∧ after.affine_ready = true ∧
      after.affine_base = roots.affine_base ∧ after.affine_rank.val = rank ∧
      written.basis = workspace.basis ∧
      tail written.factors (after.stride.val * after.stride.val) =
        tail workspace.factors (roots.stride.val * roots.stride.val) ∧
      written.stack.val[roots.pending.val]? = some frame ∧
      frame.next_direction.val = rank ∧ frame.split_checked = 1#u32 ∧
      (∀ i < frame.coefficient_start.val, written.factors[i]! = workspace.factors[i]!) ∧
      (∀ slot < roots.pending.val, written.stack.val[slot]? = workspace.stack.val[slot]?) ∧
      ∀ point : Field,
        ((activeFactor after written).IsRoot point ↔ (activeFactor roots workspace).IsRoot point ∧
          point ∈ coset (toField after.affine_base.bv) (prefixDirections basis.to_slice after.affine_rank.val)) ∧
        ((pendingFactor written frame).IsRoot point ↔ (activeFactor roots workspace).IsRoot point ∧
          point ∈ coset (toField (written.factors[frame.coefficient_start.val + after.stride.val - 1]!).bv)
            (prefixDirections basis.to_slice frame.next_direction.val))

theorem native_affine_divide_handoff : ActualNativeAffineDivideHandoff := by
  intro K kernels locator roots workspace meter paid finalMeter capacity budget basis invariant affine affineReady
    rankPositive rankBound direction directions mul raw reduce inverse charged assembly buffers trace rank prior classifies
  have degreeBound := traversal_degree_budget locator roots workspace capacity budget invariant
  have degreeMin : 2 ≤ roots.degree.val := by have := prior.proper; omega
  have positive : 0 < roots.degree.val := by omega
  have degreeRoom : roots.degree.val < roots.stride.val := by have := invariant.live; unfold liveDegree at this; omega
  have mass : factorDegreeMass roots workspace.stack ≤ budget := invariant.mass.trans_le invariant.degreeBudget
  have positiveSlots := pending_degrees_positive locator roots workspace capacity budget invariant
  have rankRoom : roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64 :=
    fun _ => ⟨rankPositive, rankBound⟩
  have basisRoom : roots.affine = true → ∃ directions, buffers.basis.directions = some directions :=
    fun _ => ⟨basis, directions⟩
  obtain ⟨length, start, reply, after, written, ran, replyEq, startValue, rightPositive, afterDegree, activeGcd,
    product, _, _, _, _, _, _, basisFrame, tableFrame, _, stride, _, earlierWords, earlierStack, frame,
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
  obtain ⟨saved, base, actualRank, savedStart, _, savedRank, savedBase⟩ :=
    committed_affine_metadata roots buffers workspace.factors workspace.stack finalMeter len offset stop
      call.2.1 call.2.2.1 call.2.2.2 commit affine basis directions
  change modelWritten.stack.val[roots.pending.val]? = some (affineSavedFrame roots len offset) at saved
  rw [actualWorkspace, frameRead] at saved
  have frameEq := Option.some.inj saved
  rw [← frameEq] at savedStart savedRank
  have baseEq : after.affine_base = roots.affine_base := actualRoots ▸ base
  have rankEq : after.affine_rank.val = rank := actualRoots ▸ actualRank
  have sameAffine : after.affine = true := actualRoots ▸ (show output.2.1.affine = true by
    simp only [output, committed, affine, ite_true])
  have sameReady : after.affine_ready = true := actualRoots ▸ (show output.2.1.affine_ready = true by
    simp only [output, committed, affine, ite_true]; exact affineReady)
  have splitChecked : frame.split_checked = 1#u32 := frameEq.symm ▸ rfl
  have translated : written.factors[frame.coefficient_start.val + after.stride.val - 1]! =
      roots.affine_base ^^^ basis[rank]! := by
    rw [stride, savedStart, ← actualWorkspace]
    exact savedBase
  have rightProduct : activeFactor roots workspace = pendingFactor written frame * activeFactor after written := by
    unfold pendingFactor pendingCoefficients
    rw [frameStart, frameLength]
    exact product
  have valid := invariant.active positive
  have squarefree : Squarefree (activeFactor roots workspace) :=
    ((nodup_roots_iff_of_splits valid.monic.ne_zero valid.split).mp valid.simple).squarefree
  refine ⟨after, written, frame, ran, preserved, traversal_rank_decreases _ _ _ _ _ _ (Or.inl smaller),
    sameAffine, sameReady, baseEq, rankEq, basisFrame, by rw [stride]; exact tableFrame invariant.live,
    frameRead, savedRank, splitChecked, ?_, earlierStack, ?_⟩
  · rw [frameStart]
    exact earlierWords
  · intro point
    rw [baseEq, rankEq, savedRank, translated]
    exact gcd_quotient_child_cosets (activeFactor roots workspace) trace (activeFactor after written)
      (pendingFactor written frame) roots.affine_base basis[rank]! basis.to_slice rank
      squarefree activeGcd rightProduct classifies point

#print axioms native_affine_divide_handoff

end BulksketchBridge.RootDivide
