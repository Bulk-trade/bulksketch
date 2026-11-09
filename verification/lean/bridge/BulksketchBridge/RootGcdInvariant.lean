import BulksketchBridge.RootInvariantReborrow
import BulksketchBridge.RootTraversalRankLinks

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient SliceKernels RebuiltLfsr BmEntry
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2100000

private theorem outcome_keeps_live_frame (roots : Roots) (buffers : FactorWork) (size : Usize) :
    let after := (outcome roots buffers size).2
    after.degree = roots.degree ∧ after.pending = roots.pending ∧ after.count = roots.count ∧
      after.stride = roots.stride ∧ after.affine = roots.affine := by
  dsimp only
  by_cases proper : 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val
  · simp only [outcome, proper, ite_true, and_self]
  · cases affine : roots.affine <;>
      simp only [outcome, proper, ite_false, affine, Bool.false_eq_true, ite_true, and_self]

/-- An admitted paid GCD step preserves the live traversal and decreases
    the rank on every successful return. -/
def ActualNativeGcdInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (locator : Polynomial Field) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget → 2 ≤ roots.degree.val →
    roots.trace_len.val ≤ roots.degree.val →
    bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Ok (), paid) →
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    DenseMul.reduceAgrees kernels → BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let buffers := buffersFor roots workspace
    let trace := prefixSlice buffers.trace roots.trace_len.val
    let factor := slicePolynomial buffers.modulus
    let tracePoly := slicePolynomial trace
    DenseGcd.Normal buffers.modulus → DenseGcd.Normal trace →
    (roots.affine = true → 0 < roots.affine_rank.val ∧ roots.affine_rank.val ≤ 64 ∧ buffers.basis.directions.isSome) →
    (roots.affine = false → roots.direction.val < 64) →
    ∃ (size : Usize) (result work : Slice U64) (raw : Slice RawProduct),
      let next := outcome roots buffers size
      let updated := { buffers with gcd := result, work, raw }
      let written := rebuild workspace roots updated
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Gcd workspace meter =
        .ok (next.1, next.2, written, id, paid) ∧
      RootTraversalInvariant locator next.2 written capacity budget ∧
      buffersFor next.2 written = updated ∧ raw.length = buffers.raw.length ∧
      (∀ stage, next.1 = .Ok (.Ok stage) →
        traversalRank stage next.2 written < traversalRank .Gcd roots workspace) ∧
      size.val = (gcd factor tracePoly).natDegree + 1 ∧
      slicePolynomial (prefixSlice result size.val) = gcd factor tracePoly ∧
      (Proper roots size →
        next.1 = .Ok (.Ok .FactorDivision) ∧
        RootDivide.ProperGcdFrame next.2 (buffersFor next.2 written) tracePoly) ∧
      (roots.affine = false → ¬ Proper roots size → factor.Splits → factor.roots.Nodup →
        TraceAgreement factor roots.splitter_seed roots.direction.val →
        (∀ point, factor.IsRoot point → (tracePoly.IsRoot point ↔
          traceBit roots.splitter_seed roots.direction.val point = 0)) →
        next.1 = .Ok (.Ok .Trace) ∧ next.2.direction.val < 64 ∧
        TraceAgreement factor roots.splitter_seed next.2.direction.val)

theorem native_gcd_invariant : ActualNativeGcdInvariant := by
  intro K kernels roots workspace meter paid locator capacity budget invariant minimum traceBound charged
    mul rawLaw reduce inverse scale buffers trace factor tracePoly aNormal bNormal affine direction
  have degreeBudget : roots.degree.val ≤ budget := by
    have mass := invariant.mass
    have bounded := invariant.degreeBudget
    unfold factorDegreeMass at mass
    omega
  obtain ⟨monic, exactDegree, _, _, _⟩ := invariant.active (by omega)
  obtain ⟨size, result, work, raw, ran, reborrow, rawWidth, sizeExact, exactGcd, proper, retry⟩ :=
    native_gcd_reborrow kernels roots workspace meter paid capacity budget invariant.buffers minimum degreeBudget
      traceBound charged mul rawLaw reduce inverse scale aNormal bNormal monic exactDegree affine direction
  let next := outcome roots buffers size
  let updated := { buffers with gcd := result, work, raw }
  let written := rebuild workspace roots updated
  obtain ⟨degreeEq, pendingEq, countEq, strideEq, affineEq⟩ := outcome_keeps_live_frame roots buffers size
  refine ⟨size, result, work, raw, ran, ?_, reborrow, rawWidth, ?_, sizeExact, exactGcd, proper, retry⟩
  · exact rebuild_preserves_traversal locator roots next.2 workspace updated capacity budget invariant
      degreeEq pendingEq countEq strideEq affineEq reborrow rfl rawWidth
  · intro stage success
    apply traversal_rank_decreases
    refine Or.inr ⟨?_, gcd_outcome_phase_step roots buffers size stage ?_ direction success⟩
    · unfold traversalPotential
      rw [degreeEq, pendingEq]
      rfl
    · intro yes
      exact ⟨(affine yes).1, (affine yes).2.1⟩

#print axioms native_gcd_invariant

end BulksketchBridge.RootRun
