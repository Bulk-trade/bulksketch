import BulksketchBridge.RootAffineRetry
import BulksketchBridge.DenseGcdSize
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootWorkspaceBudget

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient SliceKernels Algebra.Gf64 Polynomial
open AffineSubspaces AffineSubspaceAlgebra
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

/-- The original paid affine GCD stage selects a proper factor division or
    retries in a strictly smaller coset containing all roots. The result
    uses the actual normalized GCD coefficient count and the row budget. -/
def ActualNativeAffineGcd : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat) (basis : Slice U64),
    BudgetBuffers workspace capacity budget → 2 ≤ roots.degree.val → roots.degree.val ≤ budget →
    roots.affine = true → roots.affine_rank.val ≤ 64 → roots.trace_len.val ≤ roots.degree.val →
    bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Ok (), paid) →
    DenseGcd.DivisionLaw nativeDivRem kernels → DenseGcd.DivisionMeaning nativeDivRem kernels →
    BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let buffers := buffersFor roots workspace
    let trace := prefixSlice buffers.trace roots.trace_len.val
    let factor := slicePolynomial buffers.modulus
    let tracePoly := slicePolynomial trace
    buffers.basis.directions.isSome →
    basisAt buffers (roots.affine_rank.val - 1) = basis[roots.affine_rank.val - 1]! →
    DenseGcd.Normal buffers.modulus → DenseGcd.Normal trace →
    factor.Monic → factor.natDegree = roots.degree.val → factor.Splits → factor.roots.Nodup →
    (∀ point, factor.IsRoot point →
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis roots.affine_rank.val)) →
    (∀ point, factor.IsRoot point → (tracePoly.IsRoot point ↔
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis (roots.affine_rank.val - 1)))) →
    ∃ (size : Usize) (result work : Slice U64) (raw : Slice RawProduct),
      size.val = (gcd factor tracePoly).natDegree + 1 ∧
      slicePolynomial (prefixSlice result size.val) = gcd factor tracePoly ∧
      let next := outcome roots buffers size
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Gcd workspace meter =
        .ok (next.1, next.2, rebuild workspace roots { buffers with gcd := result, work, raw }, id, paid) ∧
      ((Proper roots size ∧ next.1 = .Ok (.Ok .FactorDivision)) ∨
        (next.1 = .Ok (.Ok .AffineSplit) ∧
          0 < next.2.affine_rank.val ∧ next.2.affine_rank.val < roots.affine_rank.val ∧
          ∀ point, factor.IsRoot point →
            point ∈ coset (toField next.2.affine_base.bv) (prefixDirections basis next.2.affine_rank.val)))

theorem native_affine_gcd : ActualNativeAffineGcd := by
  intro K kernels roots workspace meter paid capacity budget basis budgetBuffers degreeMin degreeBound
    affine rankBound traceRoom charged law meaning inverse scale buffers trace factor tracePoly
    directions direction modulusNormal traceNormal monic degree split simple contains classifies
  obtain ⟨⟨polyRoom, tableRoom⟩, modulusWidth, traceWidth, gcdWidth, workRoom, rawRoom⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget budgetBuffers degreeMin degreeBound
  have traceWidthBound : trace.length ≤ buffers.trace.length := by
    rw [RebuiltLfsr.prefix_length]; omega
  have limit : max buffers.modulus.length trace.length = roots.degree.val + 1 := by
    rw [modulusWidth, max_eq_left]
    rw [traceWidth] at traceWidthBound
    omega
  have gcdFit : max buffers.modulus.length trace.length ≤ buffers.gcd.length := by
    rw [limit, gcdWidth]
  have workFit : 4 * (max buffers.modulus.length trace.length + 1) ≤ buffers.work.length := by
    rw [limit, show roots.degree.val + 1 + 1 = roots.degree.val + 2 by omega]
    exact workRoom
  have rawFit : 2 * (max buffers.modulus.length trace.length + 1) ≤ buffers.raw.length := by
    rw [limit, show roots.degree.val + 1 + 1 = roots.degree.val + 2 by omega]
    exact rawRoom
  have degreeLower : 2 ≤ factor.natDegree := by rwa [degree]
  have rankPositive := affine_rank_positive factor (toField roots.affine_base.bv) basis roots.affine_rank.val
    degreeLower monic.ne_zero split simple contains
  obtain ⟨size, result, work, raw, ran, _, _, exactGcd⟩ :=
    DenseGcd.monic_gcd_meaning nativeDivRem kernels buffers.modulus trace buffers.gcd buffers.work buffers.raw
      law meaning inverse scale modulusNormal traceNormal gcdFit workFit rawFit
  have sizeExact := (DenseGcd.native_gcd_size nativeDivRem kernels buffers.modulus trace buffers.gcd buffers.work
    buffers.raw law meaning inverse scale modulusNormal traceNormal gcdFit workFit rawFit size result work raw ran).2
    (fun zero => monic.ne_zero ((gcd_eq_zero_iff factor tracePoly).mp zero).1)
  change size.val = (gcd factor tracePoly).natDegree + 1 at sizeExact
  have admitted : AfterGcdReady roots buffers size :=
    ⟨by omega, fun _ _ => ⟨rankPositive, fun _ => ⟨directions, rankBound⟩⟩,
      fun _ no => by rw [affine] at no; cases no⟩
  have exactStage := run_gcd_paid nativeCalls nativeDivRem kernels roots workspace meter paid polyRoom tableRoom
    traceRoom charged size result work raw ran admitted
  refine ⟨size, result, work, raw, sizeExact, exactGcd, exactStage, ?_⟩
  by_cases proper : Proper roots size
  · left
    refine ⟨proper, ?_⟩
    unfold outcome
    rw [ite_eq_left (show 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val from proper)]
  · right
    obtain ⟨stage, smaller, retained⟩ := affine_gcd_retry roots buffers basis size factor tracePoly affine
      rankPositive monic degree sizeExact proper direction contains classifies
    have remains := affine_rank_positive factor (toField (outcome roots buffers size).2.affine_base.bv)
      basis (outcome roots buffers size).2.affine_rank.val degreeLower monic.ne_zero split simple retained
    exact ⟨stage, remains, by omega, retained⟩

#print axioms native_affine_gcd

end BulksketchBridge.RootRun
