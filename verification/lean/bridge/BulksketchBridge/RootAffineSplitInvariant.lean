import BulksketchBridge.RootTraversalFactor
import BulksketchBridge.RootNativeAffineSplit
import BulksketchBridge.RootInvariantReborrow
import BulksketchBridge.AffineEnumerationCoset
import BulksketchBridge.RootAffineChildren
import BulksketchBridge.RootAffineTableWindow
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootReborrow

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient SliceKernels Algebra.Gf64 Polynomial
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open AffineSubspaces AffineSubspaceAlgebra AffineEnumerate
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

def ActualNativeAffineSplitInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat) (basis : Slice U64),
    RootTraversalInvariant locator roots workspace capacity budget → 3 ≤ roots.degree.val →
    roots.affine_rank.val ≤ budget → roots.affine_rank.val ≤ 64 →
    roots.affine_rank.val ≤ basis.length → IndependentDirections basis →
    ExactThrough basis (BmEntry.tail workspace.factors (roots.stride.val * roots.stride.val)) roots.affine_rank.val →
    charge meter (.AffineSplit roots.degree roots.affine_rank) = .ok (.Ok (), paid) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    AffineLinearEval.CorrectArithmetic kernels → TimesXMod.ExactScaleXor kernels →
    let buffers := buffersFor roots workspace
    let rank := roots.affine_rank.val - 1
    let factor := slicePolynomial buffers.modulus
    CorrectTable buffers.modulus buffers.table roots.degree.val →
    BackendSquareLaw kernels buffers.modulus buffers.table roots.degree.val →
    (∀ point, factor.IsRoot point → point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis roots.affine_rank.val)) →
    ∃ (size : Usize) (trace work : Slice U64) (raw : Slice RawProduct),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineSplit workspace meter =
        .ok (frame (.Ok (.Ok .Gcd)) roots { roots with trace_len := size } workspace { buffers with trace, work, raw } paid) ∧
      let after := { roots with trace_len := size }
      let next := { buffers with trace, work, raw }
      let written := rebuild workspace roots next
      RootTraversalInvariant locator after written capacity budget ∧
      CorrectTable (buffersFor after written).modulus (buffersFor after written).table after.degree.val ∧
      DenseGcd.Normal (buffersFor after written).modulus ∧
      traversalRank .Gcd after written < traversalRank .AffineSplit roots workspace ∧
      size.val ≤ roots.degree.val ∧ DenseGcd.Normal (prefixSlice trace size.val) ∧
      buffersFor { roots with trace_len := size }
        (rebuild workspace roots { buffers with trace, work, raw }) = { buffers with trace, work, raw } ∧
      RootDivide.AffineSplitClassifier (activeFactor after written) (slicePolynomial (prefixSlice trace size.val))
        roots.affine_base basis[rank]! basis rank

theorem native_affine_split_invariant : ActualNativeAffineSplitInvariant := by
  intro K kernels locator roots workspace meter paid capacity budget basis invariant minimum rankBudget
    rankMax rankBasis independent exactTable charged rawLaw squareLaw reduce arithmetic scale
    buffers rank factor correct backend contains
  have degreeBound := traversal_degree_budget locator roots workspace capacity budget invariant
  obtain ⟨monic, exactDegree, split, simple, _⟩ := invariant.active (by omega)
  have rankPositive := affine_rank_positive (activeFactor roots workspace) (toField roots.affine_base.bv)
    basis roots.affine_rank.val (by omega) monic.ne_zero split simple contains
  obtain ⟨size, trace, work, raw, ran, rawWidth, traceBound, traceNormal, reborrow, classifier⟩ :=
    native_affine_split kernels roots workspace meter paid capacity budget basis invariant.buffers
      minimum degreeBound invariant.stride rankPositive rankBudget rankMax rankBasis independent exactTable
      charged rawLaw squareLaw reduce arithmetic scale
      (traversal_monic_word locator roots workspace capacity budget invariant (by omega))
      correct backend contains
  let after := { roots with trace_len := size }
  let next := { buffers with trace, work, raw }
  let written := rebuild workspace roots next
  have preserved : RootTraversalInvariant locator after written capacity budget :=
    rebuild_preserves_traversal locator roots after workspace next capacity budget invariant
      rfl rfl rfl rfl rfl reborrow rfl rawWidth
  have sameFactor : activeFactor after written = activeFactor roots workspace := by
    change slicePolynomial (buffersFor after written).modulus = slicePolynomial buffers.modulus
    rw [reborrow]
  refine ⟨size, trace, work, raw, ran, preserved, ?_, ?_, ?_, traceBound, traceNormal, reborrow, ?_⟩
  · rw [reborrow]
    exact correct
  · exact traversal_modulus_normal locator after written capacity budget preserved (by exact Nat.le_of_succ_le minimum)
  · apply traversal_rank_decreases
    exact Or.inr ⟨rfl, .affineSplit _⟩
  · rw [sameFactor]
    exact classifier

#print axioms native_affine_split_invariant

end BulksketchBridge.RootRun
