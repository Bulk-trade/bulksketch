import BulksketchBridge.RootAffinePreparationFrame
import BulksketchBridge.RootTraversalStart
import BulksketchBridge.RootReducerInvariant

namespace BulksketchBridge.AffineSelector

open Aeneas Aeneas.Std

/-- A selected enumeration fits a native usize shift on both supported
    platform widths. The original cost comparison supplies the bound. -/
theorem selected_enumeration_rank (degree rank : Usize)
    (minimum : 3 ≤ degree.val) (degreeBound : degree.val ≤ 64) (rankBound : rank.val ≤ 64)
    (chosen : bulksketch.decode.affine.enumerate_preferred degree rank = .ok true) :
    rank.val < System.Platform.numBits := by
  rw [enumerate_preferred_refines degree rank, enumerationModel,
    Nat.mod_eq_of_lt (by omega : rank.val < 2 ^ 32)] at chosen
  dsimp only at chosen
  by_cases shift : rank.val < 64
  · rw [ite_eq_left shift] at chosen
    have lanes : 6 * degree.val ≤ U64.max := by rw [U64.max_eq]; omega
    have squareBound : squareCount degree.val ≤ 704 := by
      unfold squareCount
      have prod : (2 * (degree.val / 2)) * ((degree.val + 7) / 8) ≤ 64 * 8 :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    have squares : squareCount degree.val ≤ U64.max := by rw [U64.max_eq]; omega
    have rankPrice : rank.val * squareCount degree.val ≤ 64 * 704 :=
      Nat.mul_le_mul rankBound squareBound
    have rankFit : rank.val * squareCount degree.val ≤ U64.max := by rw [U64.max_eq]; omega
    have extra : 85 * degree.val ≤ U64.max := by rw [U64.max_eq]; omega
    have splitFit : rank.val * squareCount degree.val + 85 * degree.val ≤ U64.max := by
      rw [U64.max_eq]
      omega
    simp only [checked, lanes, ite_true, bind_ok, word_val _ lanes] at chosen
    split at chosen
    · simp only [ite_true, bind_ok, word_val _ squares, rankFit, word_val _ rankFit,
        word_val _ extra, splitFit, word_val _ splitFit] at chosen
      have affordable : ((2 ^ rank.val + 7) / 8) * (6 * degree.val) ≤
          rank.val * squareCount degree.val + 85 * degree.val :=
        of_decide_eq_true (Result.ok_injective chosen)
      have narrow : rank.val < 16 := by
        by_contra! wide
        have power : 2 ^ 16 ≤ (2 : Nat) ^ rank.val :=
          Nat.pow_le_pow_right (by decide) wide
        have blocks : 8192 ≤ (2 ^ rank.val + 7) / 8 := by omega
        have price : 8192 * 18 ≤ ((2 ^ rank.val + 7) / 8) * (6 * degree.val) :=
          Nat.mul_le_mul blocks (by omega)
        omega
      rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> omega
    · exact Bool.noConfusion (Result.ok_injective chosen)
  · rw [ite_eq_right shift] at chosen
    exact Bool.noConfusion (Result.ok_injective chosen)

end BulksketchBridge.AffineSelector

namespace BulksketchBridge.RootRun

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry Polynomial Algebra.Gf64
open DenseReducerAlgebra DenseReducerSquare AffineSubspaceAlgebra AffineSubspaces AffineEnumerate SliceKernels
open RootAffinePreparation (NativeArena native_preparation_coset native_preparation_frame)
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

/-- The factor arena can be reused at the first preparation because no
    live pending slot exists until an already prepared factor divides. -/
structure AffinePreparationEntry (roots : Roots) : Prop where
  affine : roots.affine = true
  unprepared : roots.affine_ready = false
  pendingEmpty : roots.pending = 0#usize
  degreeMin : 3 ≤ roots.degree.val
  degreeMax : roots.degree.val ≤ 64

/-- Exact shared readiness and branch-specific input for the next
    original affine stage. -/
structure AffinePreparedStage (stage : Stage) (roots : Roots) (workspace : RowWorkspace)
    (directions : Array U64 64#usize) : Prop where
  affine : roots.affine = true
  prepared : roots.affine_ready = true
  directionsEq : workspace.basis.directions = some directions
  basisLen : workspace.basis.len = UScalar.cast .U32 roots.affine_rank
  rankPositive : 0 < roots.affine_rank.val
  rankBound : roots.affine_rank.val ≤ roots.degree.val
  width : (prefixSlice directions.to_slice roots.affine_rank.val).length = roots.affine_rank.val
  independent : IndependentDirections (prefixSlice directions.to_slice roots.affine_rank.val)
  contains : ∀ point, (activeFactor roots workspace).IsRoot point →
    point ∈ coset (toField roots.affine_base.bv)
      (prefixDirections (prefixSlice directions.to_slice roots.affine_rank.val) roots.affine_rank.val)
  next : match stage with
    | .AffineEnumeration => roots.affine_rank.val < System.Platform.numBits
    | .AffineSplit => ExactThrough (prefixSlice directions.to_slice roots.affine_rank.val)
        (tail workspace.factors (roots.stride.val * roots.stride.val)) roots.affine_rank.val
    | _ => False

/-- The first stage selection from the original initialized state can
    only request affine preparation with an empty pending stack. -/
theorem initial_affine_preparation_entry (roots : Roots) (degree : Usize)
    (empty : roots.pending = 0#usize)
    (nextStage : tableStage (RootSetup.startedRoots roots degree
      (roots.v3 && decide (3 ≤ degree.val ∧ degree.val ≤ 18))) = .AffinePreparation) :
    AffinePreparationEntry (RootSetup.startedRoots roots degree
      (roots.v3 && decide (3 ≤ degree.val ∧ degree.val ≤ 18))) := by
  have affine : (roots.v3 && decide (3 ≤ degree.val ∧ degree.val ≤ 18)) = true := by
    by_contra! disabled
    simp only [tableStage, RootSetup.startedRoots, Bool.eq_false_iff.mpr disabled,
      Bool.false_eq_true, ite_false] at nextStage
    cases nextStage
  have bounds := of_decide_eq_true ((Bool.and_eq_true_iff.mp affine).2)
  exact ⟨affine, rfl, empty, bounds.1, bounds.2.trans (by decide)⟩

/-- The exact reducer step that first chooses affine preparation retains
    the initialized roots and installs its admitted reducer table. -/
def ActualNativeFirstAffinePreparationEntry : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (degree : Usize) (workspace : RowWorkspace)
    (meter paid : WorkMeter) (capacity budget : Nat),
    let after := RootSetup.startedRoots roots degree
      (roots.v3 && decide (3 ≤ degree.val ∧ degree.val ≤ 18))
    RootTraversalInvariant locator after workspace capacity budget →
    roots.pending = 0#usize → tableStage after = .AffinePreparation →
    TimesXMod.ExactScaleXor kernels →
    charge meter (.Table after.degree) = .ok (.Ok (), paid) →
    ∃ written,
      Roots.run nativeCalls nativeDivRem dictionary kernels after .ReducerPreparation workspace meter =
        .ok (.Ok (.Ok .AffinePreparation), after, written, id, paid) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      AffinePreparationEntry after ∧
      CorrectTable (buffersFor after written).modulus (buffersFor after written).table after.degree.val ∧
      traversalRank .AffinePreparation after written < traversalRank .ReducerPreparation after workspace

theorem native_first_affine_preparation_entry : ActualNativeFirstAffinePreparationEntry := by
  intro K kernels locator roots degree workspace meter paid capacity budget after invariant empty stage scale charged
  have entry : AffinePreparationEntry after := initial_affine_preparation_entry roots degree empty stage
  obtain ⟨written, ran, preserved, table, decreased⟩ :=
    native_reducer_invariant kernels locator after workspace meter paid capacity budget
      invariant entry.degreeMin scale charged
  rw [stage] at ran decreased
  exact ⟨written, ran, preserved, entry, table, decreased⟩

theorem preparation_arena_of_traversal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace) (capacity budget : Nat)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget)
    (entry : AffinePreparationEntry roots) (budgetCap : budget ≤ capacity)
    (correct : CorrectTable (buffersFor roots workspace).modulus (buffersFor roots workspace).table roots.degree.val)
    (backend : BackendSquareLaw kernels (buffersFor roots workspace).modulus
      (buffersFor roots workspace).table roots.degree.val) :
    NativeArena kernels roots workspace := by
  have degreeBudget := traversal_degree_budget locator roots workspace capacity budget invariant
  have sized := invariant.buffers
  have minimum := entry.degreeMin
  obtain ⟨layout, rawRoom⟩ :=
    affine_matrices_of_budget roots workspace capacity budget sized (by omega) degreeBudget budgetCap
  have squareRoom : roots.stride.val * roots.stride.val ≤ workspace.factors.length :=
    (Nat.mul_le_mul invariant.stride invariant.stride).trans (by have := sized.factors; omega)
  have monic := traversal_monic_word locator roots workspace capacity budget invariant (by omega)
  change (prefixSlice workspace.polynomials (roots.degree.val + 1))[roots.degree.val]! = 1#u64 at monic
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_take_of_lt (Nat.lt_succ_self roots.degree.val)] at monic
  exact ⟨minimum, entry.degreeMax, by have := sized.polynomials; omega,
    (budget_table_mono degreeBudget).trans sized.squareTable,
    by have := sized.bm; omega, layout, squareRoom, rawRoom,
    (by simpa only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using monic), correct, backend⟩

def ActualNativeAffinePreparationInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid : WorkMeter) (capacity budget : Nat),
    RootTraversalInvariant locator roots workspace capacity budget →
    AffinePreparationEntry roots → budget ≤ capacity →
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels →
    BmTerminal.NativeInverse kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    SquareAgrees kernels → DenseMul.reduceAgrees kernels → AffineLinearEval.CorrectArithmetic kernels →
    CorrectTable (buffersFor roots workspace).modulus (buffersFor roots workspace).table roots.degree.val →
    BackendSquareLaw kernels (buffersFor roots workspace).modulus (buffersFor roots workspace).table roots.degree.val →
    charge meter (.AffinePreparation roots.degree) = .ok (.Ok (), paid) →
    ∃ (stage : Stage) (after : Roots) (written : RowWorkspace) (directions : Array U64 64#usize),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffinePreparation workspace meter =
        .ok (.Ok (.Ok stage), after, written, id, paid) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      AffinePreparedStage stage after written directions ∧ after.pending = 0#usize ∧
      written.stack = workspace.stack ∧ workspaceLengths written = workspaceLengths workspace ∧
      CorrectTable (buffersFor after written).modulus (buffersFor after written).table after.degree.val ∧
      BackendSquareLaw kernels (buffersFor after written).modulus (buffersFor after written).table after.degree.val ∧
      traversalRank stage after written < traversalRank .AffinePreparation roots workspace

theorem native_affine_preparation_invariant : ActualNativeAffinePreparationInvariant := by
  intro K kernels locator roots workspace meter paid capacity budget invariant entry budgetCap
    scale mul inverse rawMul square reduce arithmetic correct backend charged
  have minimum := entry.degreeMin
  have positive : 0 < roots.degree.val := by omega
  have arena := preparation_arena_of_traversal kernels locator roots workspace capacity budget
    invariant entry budgetCap correct backend
  have valid := invariant.active positive
  have degreeBudget := traversal_degree_budget locator roots workspace capacity budget invariant
  obtain ⟨stage, base, rank, directions, written, branch, prepared, directionEq, lenEq,
      rankDegree, basisWidth, independent, _, table, contains⟩ :=
    native_preparation_coset kernels roots workspace meter paid capacity budget arena invariant.buffers
      degreeBudget invariant.stride scale mul inverse rawMul square reduce arithmetic charged valid.split valid.simple
  let after := { roots with affine_ready := true, affine_base := base, affine_rank := rank }
  change Roots.prepare_affine nativeCalls.preparation RootAffinePreparation.dictionary kernels roots workspace meter =
    .ok (.Ok (.Ok stage), after, written, id, paid) at prepared
  obtain ⟨widths, polynomials, squareTable, emitted, stack, enumDecision⟩ :=
    native_preparation_frame kernels roots after workspace written meter paid stage arena scale mul inverse rawMul
      square reduce charged prepared
  have pendingEmpty : after.pending = 0#usize := entry.pendingEmpty
  have sameFactor : activeFactor after written = activeFactor roots workspace := by
    unfold activeFactor
    rw [polynomials]
  have samePending : pendingProduct written after.pending.val = pendingProduct workspace roots.pending.val := by
    simp only [pendingProduct, pendingEmpty, entry.pendingEmpty, show (0#usize).val = 0 from rfl,
      Finset.range_zero, Finset.prod_empty]
  have sameProduct : activeTraversalProduct after written = activeTraversalProduct roots workspace := by
    unfold activeTraversalProduct traversalProduct liveProduct emittedProduct
    rw [samePending, sameFactor, emitted]
  have sameMass : factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack := by
    rw [stack]
    rfl
  have sameLive : liveDegree after written.stack = liveDegree roots workspace.stack := by
    rw [stack]
    rfl
  have preserved : RootTraversalInvariant locator after written capacity budget := by
    refine ⟨budget_buffers_same_lengths workspace written capacity budget invariant.buffers widths,
      invariant.degreeBudget, empty_pending_layout after written pendingEmpty ?_, sameProduct.trans invariant.represented,
      sameMass.trans invariant.mass, invariant.stride, sameLive ▸ invariant.live, fun _ => pendingEmpty,
      ?_, ?_⟩
    · rw [polynomials]
      exact invariant.layout.polynomialRoom
    · intro afterPositive
      rw [sameFactor]
      exact invariant.active afterPositive
    · intro slot live
      rw [pendingEmpty] at live
      exact (Nat.not_lt_zero slot live).elim
  let basis := prefixSlice directions.to_slice rank.val
  have membership (point : Field) (root : (activeFactor after written).IsRoot point) :
      point ∈ coset (toField base.bv) (prefixDirections basis rank.val) := by
    rw [sameFactor] at root
    rw [← basisWidth]
    exact contains point root
  have rankPositive := affine_rank_positive (activeFactor after written) (toField base.bv) basis rank.val
    (by rw [sameFactor, valid.exactDegree]; omega)
    (by rw [sameFactor]; exact valid.monic.ne_zero) (by rw [sameFactor]; exact valid.split)
    (by rw [sameFactor]; exact valid.simple) membership
  have stageReady : AffinePreparedStage stage after written directions := by
    refine ⟨entry.affine, rfl, directionEq, lenEq, rankPositive, rankDegree, basisWidth, independent, membership, ?_⟩
    rcases branch with rfl | rfl
    · exact AffineSelector.selected_enumeration_rank roots.degree rank minimum entry.degreeMax
        (rankDegree.trans entry.degreeMax) (enumDecision rfl)
    · exact table rfl
  have unchangedTable : (buffersFor after written).modulus = (buffersFor roots workspace).modulus ∧
      (buffersFor after written).table = (buffersFor roots workspace).table := by
    simp only [buffersFor, RootSetup.workRegions, polynomials, squareTable, after, and_self]
  refine ⟨stage, after, written, directions, ?_, preserved, stageReady, pendingEmpty, stack, widths, ?_, ?_, ?_⟩
  · rw [original_root_run_refines kernels roots .AffinePreparation workspace meter trivial]
    exact prepared
  · rw [unchangedTable.1, unchangedTable.2]
    exact correct
  · rw [unchangedTable.1, unchangedTable.2]
    exact backend
  · apply traversal_rank_decreases
    exact Or.inr ⟨by rw [stack]; rfl, preparation_phase_step roots after stage (Or.symm branch)⟩

/-- A failed first charge exits before any affine scratch can be reused. -/
def ActualNativeAffinePreparationChargeExit : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter finalMeter : WorkMeter) (error : DecodeError),
    charge meter (.AffinePreparation roots.degree) = .ok (.Err error, finalMeter) →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffinePreparation workspace meter =
      .ok (.Err error, roots, workspace, id, finalMeter)

theorem native_affine_preparation_charge_exit : ActualNativeAffinePreparationChargeExit := by
  intro K kernels roots workspace meter finalMeter error rejected
  have paidModel : StageCharge.chargeResult meter (affinePreparationCost roots.degree) = (.Err error, finalMeter) := by
    have exactCharge := roots_charge_returns meter (.AffinePreparation roots.degree)
      (affinePreparationCost roots.degree) (affine_preparation_cost_refines roots.degree)
    rw [rejected] at exactCharge
    exact Result.ok_injective exactCharge.symm
  have ready (paid : WorkMeter)
      (charged : charge meter (.AffinePreparation roots.degree) = .ok (.Ok (), paid)) :
      RootAffinePreparation.Ready nativeCalls.preparation kernels roots workspace := by
    have reply := congrArg Prod.fst (Result.ok_injective (rejected.symm.trans charged))
    cases reply
  rw [original_root_run_refines kernels roots .AffinePreparation workspace meter trivial]
  change Roots.prepare_affine nativeCalls.preparation RootAffinePreparation.dictionary kernels roots workspace meter = _
  rw [RootAffinePreparation.prepare_affine_refines nativeCalls.preparation kernels roots workspace meter ready]
  simp only [RootAffinePreparation.expected, paidModel]
  rfl

#print axioms native_affine_preparation_charge_exit
#print axioms native_first_affine_preparation_entry
#print axioms native_affine_preparation_invariant

end BulksketchBridge.RootRun
