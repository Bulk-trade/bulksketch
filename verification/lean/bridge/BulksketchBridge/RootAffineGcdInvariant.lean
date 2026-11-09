import BulksketchBridge.RootTraversalFactor
import BulksketchBridge.RootGcdInvariant
import BulksketchBridge.RootAffineRetry
import BulksketchBridge.DenseGcdSize
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootWorkspaceBudget

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient SliceKernels Algebra.Gf64 Polynomial
open AffineSubspaces AffineSubspaceAlgebra
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 4400000

/-- The original paid affine GCD stage selects a proper factor division or
    retries in a strictly smaller coset containing all roots. The result
    uses the actual normalized GCD coefficient count and the row budget. -/
def ActualNativeAffineGcdInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat) (basis : Slice U64),
    RootTraversalInvariant locator roots workspace capacity budget → 2 ≤ roots.degree.val →
    roots.affine = true → roots.affine_rank.val ≤ 64 → roots.trace_len.val ≤ roots.degree.val →
    bulksketch.decode.roots.charge meter (.Gcd roots.degree) = .ok (.Ok (), paid) →
    DenseDivRem.MulWordLaw kernels → DenseMulConvolutionSpec.RawMulAgrees kernels → DenseMul.reduceAgrees kernels →
    BmTerminal.NativeInverse kernels → TimesXMod.ExactScaleXor kernels →
    let buffers := buffersFor roots workspace
    let trace := prefixSlice buffers.trace roots.trace_len.val
    let factor := slicePolynomial buffers.modulus
    let tracePoly := slicePolynomial trace
    buffers.basis.directions.isSome →
    basisAt buffers (roots.affine_rank.val - 1) = basis[roots.affine_rank.val - 1]! →
    DenseGcd.Normal trace →
    (∀ point, factor.IsRoot point →
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis roots.affine_rank.val)) →
    (∀ point, factor.IsRoot point → (tracePoly.IsRoot point ↔
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis (roots.affine_rank.val - 1)))) →
    ∃ (size : Usize) (result work : Slice U64) (raw : Slice RawProduct) (stage : Stage),
      let next := outcome roots buffers size
      let after := next.2
      let updated := { buffers with gcd := result, work, raw }
      let written := rebuild workspace roots updated
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Gcd workspace meter =
        .ok (.Ok (.Ok stage), after, written, id, paid) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      buffersFor after written = updated ∧
      written.basis = workspace.basis ∧ written.factors = workspace.factors ∧
      activeFactor after written = factor ∧
      traversalRank stage after written < traversalRank .Gcd roots workspace ∧
      ((stage = .FactorDivision ∧ RootDivide.ProperGcdFrame after (buffersFor after written) tracePoly) ∨
        (stage = .AffineSplit ∧ 0 < after.affine_rank.val ∧
          after.affine_rank.val < roots.affine_rank.val ∧
          ∀ point, (activeFactor after written).IsRoot point →
            point ∈ coset (toField after.affine_base.bv) (prefixDirections basis after.affine_rank.val)))

theorem native_affine_gcd_invariant : ActualNativeAffineGcdInvariant := by
  intro K kernels locator roots workspace meter paid capacity budget basis invariant minimum
    affine rankBound traceRoom charged mul rawLaw reduce inverse scale buffers trace factor tracePoly
    directions direction normal contains classifies
  obtain ⟨monic, exactDegree, split, simple, _⟩ := invariant.active (by omega)
  have positive := affine_rank_positive factor (toField roots.affine_base.bv) basis roots.affine_rank.val
    (by change 2 ≤ (activeFactor roots workspace).natDegree; omega) monic.ne_zero split simple contains
  obtain ⟨size, result, work, raw, ran, preserved, reborrow, _, ranks, sizeExact, _, proper, _⟩ :=
    native_gcd_invariant kernels roots workspace meter paid locator capacity budget invariant minimum
      traceRoom charged mul rawLaw reduce inverse scale
      (traversal_modulus_normal locator roots workspace capacity budget invariant minimum) normal
      (fun _ => ⟨positive, rankBound, directions⟩) (by simp [affine])
  let next := outcome roots buffers size
  let written := rebuild workspace roots { buffers with gcd := result, work, raw }
  have factorEq : activeFactor next.2 written = factor := by
    change slicePolynomial (buffersFor next.2 written).modulus = slicePolynomial buffers.modulus
    rw [reborrow]
  by_cases divides : Proper roots size
  · obtain ⟨success, ready⟩ := proper divides
    refine ⟨size, result, work, raw, .FactorDivision, ?_, preserved, reborrow, rfl, rfl,
      factorEq, ranks _ success, Or.inl ⟨rfl, ready⟩⟩
    rw [← success]
    exact ran
  · obtain ⟨success, exactRank, retained⟩ :=
      affine_gcd_retry roots buffers basis size factor tracePoly affine positive monic exactDegree
        sizeExact divides direction contains classifies
    have remains := affine_rank_positive factor (toField next.2.affine_base.bv) basis next.2.affine_rank.val
      (by change 2 ≤ (activeFactor roots workspace).natDegree; omega) monic.ne_zero split simple retained
    refine ⟨size, result, work, raw, .AffineSplit, ?_, preserved, reborrow, rfl, rfl,
      factorEq, ranks _ success, Or.inr ⟨rfl, remains, by omega, ?_⟩⟩
    · rw [← success]
      exact ran
    · intro point root
      change (activeFactor next.2 written).IsRoot point at root
      have member : factor.IsRoot point := Eq.mp (congrArg (fun p : Polynomial Field => p.IsRoot point) factorEq) root
      exact retained point member

#print axioms native_affine_gcd_invariant

end BulksketchBridge.RootRun
