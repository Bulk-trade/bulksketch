import BulksketchBridge.RootAffineSplitInvariant
import BulksketchBridge.RootAffineGcdInvariant

namespace BulksketchBridge.RootRun

open Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open AffineSubspaces AffineSubspaceAlgebra AffineEnumerate
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

/-- Readiness carried across an affine splitter retry. Its subspace rank
uses the row budget since it can exceed the active degree after a split. -/
structure AffineSplitReady (roots : Roots) (workspace : RowWorkspace)
    (basis : Slice U64) (budget : Nat) : Prop where
  affine : roots.affine = true
  minimum : 3 ≤ roots.degree.val
  rankBudget : roots.affine_rank.val ≤ budget
  rankMax : roots.affine_rank.val ≤ 64
  rankBasis : roots.affine_rank.val ≤ basis.length
  independent : IndependentDirections basis
  directions : (buffersFor roots workspace).basis.directions.isSome
  basisWords : ∀ i < roots.affine_rank.val, basisAt (buffersFor roots workspace) i = basis[i]!
  table : ExactThrough basis (BmEntry.tail workspace.factors (roots.stride.val * roots.stride.val)) roots.affine_rank.val
  reducer : CorrectTable (buffersFor roots workspace).modulus (buffersFor roots workspace).table roots.degree.val
  contains : ∀ point, (activeFactor roots workspace).IsRoot point →
    point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis roots.affine_rank.val)

private theorem affine_gcd_keeps_layout (roots : Roots) (buffers : FactorWork) (size : Usize)
    (affine : roots.affine = true) :
    let after := (outcome roots buffers size).2
    after.degree = roots.degree ∧ after.stride = roots.stride ∧ after.trace_len = roots.trace_len ∧
      after.affine = true := by
  dsimp only
  by_cases proper : 0 < size.val - 1 ∧ size.val - 1 < roots.degree.val <;>
    simp only [outcome, proper, affine, ite_true, ite_false, and_self]

/-- The original Split and GCD share the exact borrowed windows. A retry
restores the same basis and table at the smaller positive rank. -/
def ActualNativeAffineSplitGcdPair : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid finalMeter : WorkMeter) (capacity budget : Nat) (basis : Slice U64),
    RootTraversalInvariant locator roots workspace capacity budget →
    AffineSplitReady roots workspace basis budget →
    charge meter (.AffineSplit roots.degree roots.affine_rank) = .ok (.Ok (), paid) →
    charge paid (.Gcd roots.degree) = .ok (.Ok (), finalMeter) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    AffineLinearEval.CorrectArithmetic kernels → TimesXMod.ExactScaleXor kernels →
    DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels →
    BackendSquareLaw kernels (buffersFor roots workspace).modulus (buffersFor roots workspace).table roots.degree.val →
    ∃ (splitRoots after : Roots) (splitWorkspace written : RowWorkspace) (next : Stage),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineSplit workspace meter =
        .ok (.Ok (.Ok .Gcd), splitRoots, splitWorkspace, id, paid) ∧
      Roots.run nativeCalls nativeDivRem dictionary kernels splitRoots .Gcd splitWorkspace paid =
        .ok (.Ok (.Ok next), after, written, id, finalMeter) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      activeFactor after written = activeFactor roots workspace ∧
      written.basis = workspace.basis ∧ written.factors = workspace.factors ∧
      traversalRank next after written < traversalRank .AffineSplit roots workspace ∧
      ((next = .FactorDivision ∧ RootDivide.ProperGcdFrame after (buffersFor after written)
        (slicePolynomial (prefixSlice (buffersFor after written).trace after.trace_len.val))) ∨
       (next = .AffineSplit ∧ after.affine_rank.val < roots.affine_rank.val ∧
        AffineSplitReady after written basis budget))

theorem native_affine_split_gcd_pair : ActualNativeAffineSplitGcdPair := by
  intro K kernels locator roots workspace meter paid finalMeter capacity budget basis invariant ready
    splitCharge gcdCharge rawLaw squareLaw reduce arithmetic scale mul inverse backend
  obtain ⟨len, trace, work, raw, splitRan, splitInvariant, splitTable, _, splitRank, traceRoom,
    traceNormal, splitReborrow, classifier⟩ :=
    native_affine_split_invariant kernels locator roots workspace meter paid capacity budget basis invariant
      ready.minimum ready.rankBudget ready.rankMax ready.rankBasis ready.independent ready.table
      splitCharge rawLaw squareLaw reduce arithmetic scale ready.reducer backend ready.contains
  let buffers := buffersFor roots workspace
  let splitRoots := { roots with trace_len := len }
  let splitWorkspace := rebuild workspace roots { buffers with trace, work, raw }
  let splitBuffers := buffersFor splitRoots splitWorkspace
  have splitWindow : splitBuffers = { buffers with trace, work, raw } := splitReborrow
  have splitFactor : activeFactor splitRoots splitWorkspace = activeFactor roots workspace := by
    change slicePolynomial splitBuffers.modulus = _
    rw [splitWindow]
    rfl
  have minimum : 3 ≤ splitRoots.degree.val := ready.minimum
  have affine : splitRoots.affine = true := ready.affine
  have directions : splitBuffers.basis.directions.isSome := by rw [splitWindow]; exact ready.directions
  obtain ⟨monic, degree, split, simple, _⟩ := invariant.active (by have := ready.minimum; omega)
  have rankPositive := affine_rank_positive (activeFactor roots workspace) (toField roots.affine_base.bv)
    basis roots.affine_rank.val (by rw [degree]; have := ready.minimum; omega)
    monic.ne_zero split simple ready.contains
  have direction : basisAt splitBuffers (splitRoots.affine_rank.val - 1) = basis[splitRoots.affine_rank.val - 1]! := by
    rw [splitWindow]
    exact ready.basisWords _ (by change roots.affine_rank.val - 1 < roots.affine_rank.val; omega)
  have normal : DenseGcd.Normal (prefixSlice splitBuffers.trace splitRoots.trace_len.val) := by
    rw [splitWindow]
    exact traceNormal
  have retained (point : Field) (root : (slicePolynomial splitBuffers.modulus).IsRoot point) :
      point ∈ coset (toField splitRoots.affine_base.bv) (prefixDirections basis splitRoots.affine_rank.val) :=
    ready.contains point (splitFactor ▸ root)
  have classifies (point : Field) (root : (slicePolynomial splitBuffers.modulus).IsRoot point) :
      (slicePolynomial (prefixSlice splitBuffers.trace splitRoots.trace_len.val)).IsRoot point ↔
      point ∈ coset (toField splitRoots.affine_base.bv) (prefixDirections basis (splitRoots.affine_rank.val - 1)) := by
    rw [splitWindow]
    exact (classifier point root).1
  obtain ⟨size, result, gcdWork, gcdRaw, next, gcdRan, gcdInvariant, gcdReborrow, sameBasis, sameFactors,
    gcdFactor, gcdRank, stage⟩ :=
    native_affine_gcd_invariant kernels locator splitRoots splitWorkspace paid finalMeter capacity budget basis splitInvariant
      (by omega) affine ready.rankMax traceRoom gcdCharge mul rawLaw reduce inverse scale
      directions direction normal retained classifies
  let after := (outcome splitRoots splitBuffers size).2
  let written := rebuild splitWorkspace splitRoots { splitBuffers with gcd := result, work := gcdWork, raw := gcdRaw }
  obtain ⟨degree, stride, traceLen, afterAffine⟩ := affine_gcd_keeps_layout splitRoots splitBuffers size affine
  refine ⟨splitRoots, after, splitWorkspace, written, next, splitRan, gcdRan, gcdInvariant,
    gcdFactor.trans splitFactor, sameBasis, sameFactors, gcdRank.trans splitRank, ?_⟩
  rcases stage with ⟨chosen, frame⟩ | ⟨chosen, _, smaller, contains⟩
  · left
    refine ⟨chosen, ?_⟩
    have exactTrace : slicePolynomial (prefixSlice (buffersFor after written).trace after.trace_len.val) =
        slicePolynomial (prefixSlice splitBuffers.trace splitRoots.trace_len.val) := by
      rw [gcdReborrow, traceLen]
    rwa [exactTrace]
  · right
    refine ⟨chosen, smaller, ?_⟩
    refine ⟨afterAffine, by rw [degree]; exact minimum, smaller.le.trans ready.rankBudget,
      smaller.le.trans ready.rankMax, smaller.le.trans ready.rankBasis, ready.independent,
      ?_, ?_, ?_, ?_, contains⟩
    · rw [gcdReborrow]
      exact directions
    · intro i active
      rw [gcdReborrow]
      change basisAt splitBuffers i = _
      rw [splitWindow]
      exact ready.basisWords i (active.trans smaller)
    · rw [sameFactors, stride]
      intro i inside
      exact ready.table i (inside.trans smaller.le)
    · rw [gcdReborrow, degree]
      exact splitTable

#print axioms native_affine_split_gcd_pair

end BulksketchBridge.RootRun
