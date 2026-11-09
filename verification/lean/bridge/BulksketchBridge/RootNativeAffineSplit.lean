import BulksketchBridge.AffineEnumerationCoset
import BulksketchBridge.RootAffineChildren
import BulksketchBridge.RootAffineTableWindow
import BulksketchBridge.NativeRootRun

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient SliceKernels Algebra.Gf64 Polynomial
open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec
open AffineSubspaces AffineSubspaceAlgebra AffineEnumerate
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

/-- The paid native split stage reads the saved table row and returns
    the exact GCD-stage frame and both child-coset tests at factor roots. -/
def ActualNativeAffineSplit : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat) (basis : Slice U64),
    BudgetBuffers workspace capacity budget → 3 ≤ roots.degree.val → roots.degree.val ≤ budget →
    roots.stride.val ≤ budget + 1 → 0 < roots.affine_rank.val →
    roots.affine_rank.val ≤ budget → roots.affine_rank.val ≤ 64 →
    roots.affine_rank.val ≤ basis.length → IndependentDirections basis →
    ExactThrough basis (BmEntry.tail workspace.factors (roots.stride.val * roots.stride.val)) roots.affine_rank.val →
    charge meter (.AffineSplit roots.degree roots.affine_rank) = .ok (.Ok (), paid) →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    AffineLinearEval.CorrectArithmetic kernels → TimesXMod.ExactScaleXor kernels →
    let buffers := buffersFor roots workspace
    let rank := roots.affine_rank.val - 1
    let factor := slicePolynomial buffers.modulus
    buffers.modulus[roots.degree.val]! = 1#u64 →
    CorrectTable buffers.modulus buffers.table roots.degree.val →
    BackendSquareLaw kernels buffers.modulus buffers.table roots.degree.val →
    (∀ point, factor.IsRoot point → point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis roots.affine_rank.val)) →
    ∃ (size : Usize) (trace work : Slice U64) (raw : Slice RawProduct),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineSplit workspace meter =
        .ok (frame (.Ok (.Ok .Gcd)) roots { roots with trace_len := size } workspace { buffers with trace, work, raw } paid) ∧
      RootDivide.AffineSplitClassifier factor (slicePolynomial (prefixSlice trace size.val))
        roots.affine_base basis[rank]! basis rank

theorem native_affine_split : ActualNativeAffineSplit := by
  intro K kernels roots workspace meter paid capacity budget basis sized degreeMin degreeBound stride
    rankPositive rankBudget rankMax basisBound independent tableExact charged rawLaw squareLaw reduceLaw
    arithmetic scale buffers rank factor monic correct backend contains
  let table := BmEntry.tail workspace.factors (roots.stride.val * roots.stride.val)
  obtain ⟨factorReady, modulusWidth, traceWidth, _, workRoom, rawRoom⟩ :=
    gcd_buffers_of_budget roots workspace capacity budget sized (by omega) degreeBound
  change buffers.modulus.length = roots.degree.val + 1 at modulusWidth
  change buffers.trace.length = roots.degree.val at traceWidth
  change 4 * (roots.degree.val + 2) ≤ buffers.work.length at workRoom
  change 2 * (roots.degree.val + 2) ≤ buffers.raw.length at rawRoom
  have tableWidth : buffers.table.length = RootSetup.tableCount roots.degree.val := by
    change (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)).length = _
    rw [RebuiltLfsr.prefix_length, Nat.min_eq_left factorReady.2]
  have paidReady := affine_window_of_budget roots workspace capacity budget sized stride rankBudget rankMax
  have ready : Ready nativeDivRem kernels roots .AffineSplit workspace meter :=
    ⟨factorReady, fun _ _ => paidReady⟩
  obtain ⟨size, trace, work, raw, splitter, eval⟩ :=
    AffineSplitter.native_splitter_at_roots kernels rawLaw squareLaw reduceLaw arithmetic scale buffers.modulus
      buffers.table (row table rank) roots.affine_base buffers.trace buffers.work buffers.raw roots.degree.val
      modulusWidth (by omega) (by omega) (by omega) (by omega) monic tableWidth correct backend
  have notZero : roots.affine_rank ≠ 0#usize := by
    intro zero
    rw [zero] at rankPositive
    exact Nat.not_lt_zero 0 rankPositive
  refine ⟨size, trace, work, raw, ?_, ?_⟩
  · rw [original_root_run_refines kernels roots .AffineSplit workspace meter ready]
    simp only [expected, affineSplit, charged, bind_ok]
    dsimp! only
    rw [ite_eq_right notZero, affine_window_is_row roots workspace.factors rankPositive]
    rw [splitter]
    simp only [bind_ok]
    rfl
  · intro point root
    have rankSucc : roots.affine_rank.val = rank + 1 := by omega
    have evaluated := eval point root
    change (slicePolynomial (prefixSlice trace size.val)).eval point =
      (rowPolynomial (row table rank)).eval point +
        (rowPolynomial (row table rank)).eval (toField roots.affine_base.bv) at evaluated
    rw [tableExact rank (by omega)] at evaluated
    have left : (slicePolynomial (prefixSlice trace size.val)).IsRoot point ↔
        point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis rank) := by
      change (slicePolynomial (prefixSlice trace size.val)).eval point = 0 ↔ _
      rw [evaluated]
      simpa only [AffineSubspaceAlgebra.splitter, eval_add, eval_C] using
        splitter_zero (toField roots.affine_base.bv) point (prefixDirections basis rank)
    have parent := contains point root
    rw [rankSucc, prefixDirections] at parent
    have children := (coset_children (toField roots.affine_base.bv) (toField basis[rank]!.bv) point
      (prefixDirections basis rank)).mp parent
    have disjoint := children_disjoint (toField roots.affine_base.bv) (toField basis[rank]!.bv)
      (prefixDirections basis rank) (independent rank (by omega))
    refine ⟨left, ?_⟩
    constructor
    · intro nonzero
      exact children.resolve_left (fun member => nonzero (left.mpr member))
    · intro right zero
      exact Set.disjoint_left.mp disjoint (left.mp zero) right

#print axioms native_affine_split

end BulksketchBridge.RootRun
