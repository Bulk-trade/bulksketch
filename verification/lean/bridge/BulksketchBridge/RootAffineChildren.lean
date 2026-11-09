import BulksketchBridge.RootDivideCommitDegree
import BulksketchBridge.RootPendingFactors
import BulksketchBridge.AffineSplitterEvaluation
import Mathlib.Algebra.Squarefree.Basic

namespace BulksketchBridge.RootDivide

open Aeneas Aeneas.Std Algebra.Gf64 DenseCoefficient RebuiltLfsr SliceKernels Polynomial
open AffineSubspaces AffineSubspaceAlgebra
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial (exact_divide_into)

set_option maxRecDepth 4096
set_option maxHeartbeats 1900000

/-- The roots of a proper GCD and its exact complementary quotient
partition the parent's roots by the splitter test. Squarefreeness
prevents a shared root of the two children. -/
theorem gcd_quotient_root_partition (parent trace left right : Polynomial Field)
    (squarefree : Squarefree parent) (gcdExact : left = gcd parent trace)
    (product : parent = right * left) (point : Field) :
    (left.IsRoot point ↔ parent.IsRoot point ∧ trace.IsRoot point) ∧
    (right.IsRoot point ↔ parent.IsRoot point ∧ ¬trace.IsRoot point) := by
  have leftTest : left.IsRoot point ↔ parent.IsRoot point ∧ trace.IsRoot point := by
    simp only [← Polynomial.dvd_iff_isRoot, gcdExact, dvd_gcd_iff]
  have productRoot : parent.IsRoot point ↔ right.IsRoot point ∨ left.IsRoot point := by
    rw [product]
    change (right * left).eval point = 0 ↔ right.eval point = 0 ∨ left.eval point = 0
    rw [eval_mul, mul_eq_zero]
  refine ⟨leftTest, ?_⟩
  constructor
  · intro rightRoot
    have parentRoot : parent.IsRoot point := productRoot.mpr (.inl rightRoot)
    refine ⟨parentRoot, ?_⟩
    intro traceRoot
    have leftRoot := leftTest.mpr ⟨parentRoot, traceRoot⟩
    have repeated : (X - C point) * (X - C point) ∣ parent := by
      rw [product]
      exact mul_dvd_mul (Polynomial.dvd_iff_isRoot.mpr rightRoot) (Polynomial.dvd_iff_isRoot.mpr leftRoot)
    exact (Polynomial.not_isUnit_X_sub_C point) (squarefree _ repeated)
  · intro root
    exact (productRoot.mp root.1).resolve_right (fun leftRoot => root.2 (leftTest.mp leftRoot).2)

/-- The abstract splitter classifier from the original affine subspace
annihilator. It is needed only at roots of the current parent. -/
def AffineSplitClassifier (parent trace : Polynomial Field)
    (base direction : U64) (basis : Slice U64) (rank : Nat) : Prop :=
  ∀ point : Field, parent.IsRoot point →
    (trace.IsRoot point ↔ point ∈ coset (toField base.bv) (prefixDirections basis rank)) ∧
    (¬trace.IsRoot point ↔ point ∈ coset (toField base.bv + toField direction.bv) (prefixDirections basis rank))

/-- Exact left and right root sets under the original splitter's coset
classifier. The right base uses the original binary-field XOR. -/
theorem gcd_quotient_child_cosets (parent trace left right : Polynomial Field)
    (base direction : U64) (basis : Slice U64) (rank : Nat)
    (squarefree : Squarefree parent) (gcdExact : left = gcd parent trace)
    (product : parent = right * left)
    (classifies : AffineSplitClassifier parent trace base direction basis rank) (point : Field) :
    (left.IsRoot point ↔ parent.IsRoot point ∧ point ∈ coset (toField base.bv) (prefixDirections basis rank)) ∧
    (right.IsRoot point ↔ parent.IsRoot point ∧
      point ∈ coset (toField (base ^^^ direction).bv) (prefixDirections basis rank)) := by
  obtain ⟨leftTest, rightTest⟩ := gcd_quotient_root_partition parent trace left right squarefree gcdExact product point
  have baseSum : toField (base ^^^ direction).bv = toField base.bv + toField direction.bv :=
    toField_xor _ _
  constructor
  · rw [leftTest]
    exact and_congr_right (fun member => (classifies point member).1)
  · rw [rightTest, baseSum]
    exact and_congr_right (fun member => (classifies point member).2)

private theorem cast_u64_value (word : Usize) : (UScalar.cast .U64 word).val = word.val := by
  have bound : word.val < 2 ^ System.Platform.numBits := word.hBounds
  have platform : 2 ^ System.Platform.numBits ≤ 2 ^ 64 :=
    Nat.pow_le_pow_right (by decide) System.Platform.numBits_le
  rw [UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (bound.trans_le platform)

def affineSavedFrame (roots : Roots) (length start : Usize) : FactorFrame :=
  ⟨UScalar.cast .U64 start, UScalar.cast .U64 length,
    UScalar.cast .U32 (ClosedLeafAdvance.usizeWord (roots.affine_rank.val - 1)), 1#u32⟩

/-- The original commit leaves the active base unchanged and writes
the right child's translated base and reduced rank in the pending slot. -/
theorem committed_affine_metadata (roots : Roots) (buffers : FactorWork)
    (factors : Slice U64) (stack : Slice FactorFrame) (meter : WorkMeter)
    (length start stop : Usize) (quotient remainder : Slice U64) (raw : Slice RawProduct)
    (commit : CommitReady roots buffers factors stack quotient length start stop)
    (affine : roots.affine = true) (basis : Array U64 64#usize) (directions : buffers.basis.directions = some basis) :
    let output := committed roots buffers factors stack meter length start quotient remainder raw
    let rank := roots.affine_rank.val - 1
    let frame := affineSavedFrame roots length start
    output.2.2.2.2.2.1.val[roots.pending.val]? = some frame ∧
    output.2.1.affine_base = roots.affine_base ∧ output.2.1.affine_rank.val = rank ∧
    frame.coefficient_start.val = start.val ∧ frame.coefficient_len.val = length.val ∧ frame.next_direction.val = rank ∧
    output.2.2.2.2.1[start.val + roots.stride.val - 1]! = roots.affine_base ^^^ basis[rank]! := by
  let rank := roots.affine_rank.val - 1
  let rankWord := ClosedLeafAdvance.usizeWord rank
  let baseSlot := ClosedLeafAdvance.usizeWord (start.val + roots.stride.val - 1)
  have rankFits : roots.affine_rank.val ≤ Usize.max := by scalar_tac
  have rankVal : rankWord.val = rank :=
    ClosedLeafAdvance.word_val _ ((Nat.sub_le ..).trans rankFits)
  have rankSmall : rank < 2 ^ 32 := by
    have := (commit.affineRank affine).2
    unfold rank
    omega
  have castRank : (UScalar.cast .U32 rankWord).val = rank := by
    rw [UScalar.cast_val_eq, rankVal]
    exact Nat.mod_eq_of_lt rankSmall
  obtain ⟨slotPositive, slotFits⟩ := commit.affineBase affine
  have baseValue : baseSlot.val = start.val + roots.stride.val - 1 :=
    ClosedLeafAdvance.word_val _ ((Nat.sub_le ..).trans (slotFits.trans factors.length_ineq))
  let frame : FactorFrame :=
    ⟨UScalar.cast .U64 start, UScalar.cast .U64 length, directionWord roots, 1#u32⟩
  let saved := { frame with next_direction := UScalar.cast .U32 rankWord }
  let copied := factors.setSlice! start.val (prefixSlice quotient length.val).val
  have frameRead : ((stack.set roots.pending frame).set roots.pending saved).val[roots.pending.val]? = some saved := by
    rw [Slice.set_val_eq]
    exact List.getElem?_set_self (by
      change roots.pending.val < (stack.set roots.pending frame).length
      rw [Slice.set_length]
      exact commit.slotRoom)
  have baseRead : (copied.set baseSlot (roots.affine_base ^^^ basis[rank]!))[start.val + roots.stride.val - 1]! =
      roots.affine_base ^^^ basis[rank]! := by
    apply Slice.getElem!_Nat_set_eq
    refine ⟨baseValue, ?_⟩
    rw [show copied.length = factors.length from Slice.setSlice!_length ..]
    omega
  dsimp only
  simp only [committed, affine, ite_true, directions, Option.map_some, Option.getD_some]
  change ((stack.set roots.pending frame).set roots.pending saved).val[roots.pending.val]? = some saved ∧
    True ∧ rankWord.val = rank ∧
    (UScalar.cast .U64 start).val = start.val ∧ (UScalar.cast .U64 length).val = length.val ∧
    (UScalar.cast .U32 rankWord).val = rank ∧
    (copied.set baseSlot (roots.affine_base ^^^ basis[rankWord.val]!))[start.val + roots.stride.val - 1]! =
      roots.affine_base ^^^ basis[rank]!
  rw [rankVal]
  exact ⟨frameRead, trivial, rfl, cast_u64_value _, cast_u64_value _, castRank, baseRead⟩

/-- The actual successful native proper division commits both affine child
cosets. The exact preceding GCD and classifier identify which roots move
to the pending child. The committed offsets and saved base are used to
read the child factors, rather than reading an abstract factor pair. -/
def ActualNativeCommittedAffineChildren : Prop :=
  ∀ (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (buffers : FactorWork) (factors : Slice U64) (stack : Slice FactorFrame)
    (meter paid finalMeter : WorkMeter) (length start stop : Usize),
    DenseDivision.RefinesModel division kernels →
    NativeDivideReady roots buffers → ProperDivideShape roots buffers →
    (nativeCall roots buffers).1 = some length →
    StageCharge.chargeResult meter (divideCost roots.degree) = (.Ok (), paid) →
    StageCharge.chargeResult paid (assemblyCost roots.degree) = (.Ok (), finalMeter) →
    Usize.checked_mul roots.pending roots.stride = some start →
    Usize.checked_add start length = some stop →
    CommitReady roots buffers factors stack (nativeCall roots buffers).2.1 length start stop →
    roots.affine = true → length.val < roots.stride.val →
    ∀ basis : Array U64 64#usize,
    buffers.basis.directions = some basis →
    Squarefree (slicePolynomial buffers.modulus) →
    slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) =
      gcd (slicePolynomial buffers.modulus) (slicePolynomial (prefixSlice buffers.trace roots.trace_len.val)) →
    AffineSplitClassifier (slicePolynomial buffers.modulus)
      (slicePolynomial (prefixSlice buffers.trace roots.trace_len.val))
      roots.affine_base basis[roots.affine_rank.val - 1]! basis.to_slice (roots.affine_rank.val - 1) →
    let call := nativeCall roots buffers
    let output := committed roots buffers factors stack finalMeter length start call.2.1 call.2.2.1 call.2.2.2
    let left := slicePolynomial (prefixSlice output.2.2.1.modulus (output.2.1.degree.val + 1))
    let frame := affineSavedFrame roots length start
    let right := slicePolynomial (ClosedLeaf.region output.2.2.2.2.1 frame.coefficient_start.val
      (frame.coefficient_start.val + frame.coefficient_len.val))
    let savedBase := output.2.2.2.2.1[frame.coefficient_start.val + roots.stride.val - 1]!
    Roots.divide (exact_divide_into division) DenseGcd.dictionary kernels roots buffers factors stack meter =
        .ok output ∧
      slicePolynomial buffers.modulus = right * left ∧ Squarefree left ∧ Squarefree right ∧
      output.2.2.2.2.2.1.val[roots.pending.val]? = some frame ∧ output.2.1.affine_rank.val = roots.affine_rank.val - 1 ∧ frame.next_direction.val = roots.affine_rank.val - 1 ∧
      (∀ point : Field,
        (left.IsRoot point ↔ (slicePolynomial buffers.modulus).IsRoot point ∧
          point ∈ coset (toField output.2.1.affine_base.bv) (prefixDirections basis.to_slice output.2.1.affine_rank.val)) ∧
        (right.IsRoot point ↔ (slicePolynomial buffers.modulus).IsRoot point ∧
          point ∈ coset (toField savedBase.bv) (prefixDirections basis.to_slice frame.next_direction.val)))

theorem native_committed_affine_children : ActualNativeCommittedAffineChildren := by
  intro division K kernels roots buffers factors stack meter paid finalMeter length start stop
    law ready shape candidate charged assembly startOk endOk commit affine lengthRoom basis directions
    squarefree gcdExact classifies
  let call := nativeCall roots buffers
  let output := committed roots buffers factors stack finalMeter length start call.2.1 call.2.2.1 call.2.2.2
  let parent := slicePolynomial buffers.modulus
  let trace := slicePolynomial (prefixSlice buffers.trace roots.trace_len.val)
  let left := slicePolynomial (prefixSlice output.2.2.1.modulus (output.2.1.degree.val + 1))
  let frame := affineSavedFrame roots length start
  let right := slicePolynomial (ClosedLeaf.region output.2.2.2.2.1 frame.coefficient_start.val
    (frame.coefficient_start.val + frame.coefficient_len.val))
  let savedBase := output.2.2.2.2.1[frame.coefficient_start.val + roots.stride.val - 1]!
  obtain ⟨native, _, positive⟩ := native_committed_degree_mass division kernels roots buffers factors stack
    meter paid finalMeter length start stop law ready shape candidate charged assembly startOk endOk commit
  obtain ⟨_, fits, _, _, decomposition⟩ := native_call_degree roots buffers ready shape length candidate
  obtain ⟨_, slotEnd⟩ := commit.affineBase affine
  obtain ⟨leftWords, rightWords⟩ := RootRun.committed_coefficients roots buffers factors stack finalMeter
    length start call.2.1 call.2.2.1 call.2.2.2 (by omega) fits (Nat.le_of_lt lengthRoom) slotEnd
    (fun _ => lengthRoom) ready.gcdRoom commit.modulusRoom
  obtain ⟨stored, leftBase, leftRank, savedStart, savedLen, savedRank, translatedBase⟩ :=
    committed_affine_metadata roots buffers factors stack finalMeter length start stop
      call.2.1 call.2.2.1 call.2.2.2 commit affine basis directions
  have leftLength : output.2.1.degree.val + 1 = roots.gcd_len.val := by
    change roots.gcd_degree.val + 1 = roots.gcd_len.val
    exact shape.gcdWidth.symm
  have leftExact : left = slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val) := by
    unfold left
    rw [leftLength]
    exact congrArg slicePolynomial leftWords
  have rightExact : right = slicePolynomial (prefixSlice call.2.1 length.val) := by
    unfold right
    rw [savedStart, savedLen]
    exact congrArg slicePolynomial rightWords
  have product : parent = right * left := by
    rw [rightExact, leftExact]
    exact decomposition
  have exactGcd : left = gcd parent trace := leftExact.trans gcdExact
  have children : Squarefree (right * left) := by
    rw [← product]
    exact squarefree
  have savedExact : savedBase = roots.affine_base ^^^ basis[roots.affine_rank.val - 1]! := by
    unfold savedBase
    rw [savedStart]
    exact translatedBase
  change Roots.divide (exact_divide_into division) DenseGcd.dictionary kernels roots buffers factors stack meter = .ok output ∧
    parent = right * left ∧ Squarefree left ∧ Squarefree right ∧
    output.2.2.2.2.2.1.val[roots.pending.val]? = some frame ∧ output.2.1.affine_rank.val = roots.affine_rank.val - 1 ∧ frame.next_direction.val = roots.affine_rank.val - 1 ∧ _
  refine ⟨native, product, children.of_mul_right, children.of_mul_left, stored, leftRank, savedRank, ?_⟩
  intro point
  change (left.IsRoot point ↔ parent.IsRoot point ∧
    point ∈ coset (toField output.2.1.affine_base.bv) (prefixDirections basis.to_slice output.2.1.affine_rank.val)) ∧
    (right.IsRoot point ↔ parent.IsRoot point ∧
    point ∈ coset (toField savedBase.bv) (prefixDirections basis.to_slice frame.next_direction.val))
  rw [leftBase, leftRank, savedExact, savedRank]
  exact gcd_quotient_child_cosets parent trace left right roots.affine_base basis[roots.affine_rank.val - 1]!
    basis.to_slice (roots.affine_rank.val - 1) squarefree exactGcd product classifies point


open DenseReducerAlgebra DenseReducerSquare DenseMulConvolutionSpec in
/-- The existing original affine subspace and splitter paths supply the
pointwise classifier used by the exact proper-division theorem. -/
theorem native_splitter_classifier {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (rawLaw : RawMulAgrees kernels) (squareLaw : SquareAgrees kernels) (reduceLaw : DenseMul.reduceAgrees kernels)
    (arithmetic : AffineLinearEval.CorrectArithmetic kernels) (scale : TimesXMod.ExactScaleXor kernels)
    (modulus table basis subspaceTable : Slice U64) (base : U64) (output work : Slice U64)
    (raw : Slice RawProduct) (degree rank : Nat)
    (shape : modulus.length = degree + 1) (minimum : 4 ≤ modulus.length)
    (outputRoom : degree ≤ output.length) (workRoom : 2 * degree ≤ work.length)
    (rawRoom : 2 * degree < raw.length)
    (monic : modulus[degree]! = 1#u64) (tableLen : table.length = degree * (degree / 2))
    (correct : CorrectTable modulus table degree) (backend : BackendSquareLaw kernels modulus table degree)
    (basisWidth : basis.length ≤ 64) (subspaceRoom : AffineSubspaces.offset (basis.length + 1) ≤ subspaceTable.length)
    (active : rank < basis.length)
    (independent : toField basis[rank]!.bv ∉ spanWords (prefixDirections basis rank))
    (parentCoset : ∀ point, (slicePolynomial modulus).IsRoot point →
      point ∈ coset (toField base.bv) (prefixDirections basis (rank + 1))) :
    ∃ filled normalized trace newWork newRaw,
      bulksketch.decode.affine.subspaces RootSetup.gf64Dictionary kernels basis subspaceTable = .ok filled ∧
      bulksketch.decode.affine.splitter RootTrace.nativeSquare RootSetup.gf64Dictionary kernels modulus table
        (AffineSubspaces.row filled rank) base output work raw = .ok (normalized, trace, newWork, newRaw) ∧
      AffineSplitClassifier (slicePolynomial modulus) (slicePolynomial (prefixSlice trace normalized.val))
        base basis[rank]! basis rank := by
  obtain ⟨filled, normalized, trace, newWork, newRaw, filledNormal, traceNormal, classified⟩ :=
    AffineSplitter.native_splitter_children kernels rawLaw squareLaw reduceLaw arithmetic scale
      modulus table basis subspaceTable base output work raw degree rank shape minimum outputRoom workRoom rawRoom
      monic tableLen correct backend basisWidth subspaceRoom active independent
  exact ⟨filled, normalized, trace, newWork, newRaw, filledNormal, traceNormal,
    fun point parent => classified point parent (parentCoset point parent)⟩

open ClosedLeafAdvance in
/-- When the original pending child is popped, its saved base and rank
apply to the exact polynomial restored by the original advance. -/
theorem advance_restores_affine_child (roots : Roots) (workspace : RowWorkspace) (frame : FactorFrame)
    (bounds : PopBounds roots workspace frame) (affine : roots.affine = true)
    (basis : Slice U64)
    (child : ∀ point : Field, (RootRun.pendingFactor workspace frame).IsRoot point →
      point ∈ coset (toField workspace.factors[frame.coefficient_start.val + roots.stride.val - 1]!.bv)
        (prefixDirections basis frame.next_direction.val)) :
    let next := poppedRoots roots workspace frame
    let written := poppedWorkspace workspace frame
    Roots.advance roots workspace = .ok (stageFor next, next, written, id) ∧
      ∀ point : Field, (RootRun.activeFactor next written).IsRoot point →
        point ∈ coset (toField next.affine_base.bv) (prefixDirections basis next.affine_rank.val) := by
  dsimp only
  refine ⟨advance_pop_refines roots workspace frame bounds, ?_⟩
  intro point root
  rw [RootRun.popped_factor roots workspace frame bounds] at root
  have castRank : (UScalar.cast .Usize frame.next_direction).val = frame.next_direction.val := by
    have source : frame.next_direction.val < 2 ^ 32 := frame.next_direction.hBounds
    have platform : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
      rcases System.Platform.numBits_eq with width | width
      · simpa only [width] using (show (2 : Nat) ^ 32 ≤ 2 ^ 32 by decide)
      · simpa only [width] using (show (2 : Nat) ^ 32 ≤ 2 ^ 64 by decide)
    rw [UScalar.cast_val_eq]
    exact Nat.mod_eq_of_lt (source.trans_le platform)
  simpa only [poppedRoots, affine, ite_true, castRank] using child point root

end BulksketchBridge.RootDivide
