import BulksketchBridge.NativeDeflateTraversalInput
import BulksketchBridge.RootTraversalStart

namespace BulksketchBridge.Deflation

open Aeneas.Std DenseCoefficient RebuiltLfsr SliceKernels Algebra.Gf64 Polynomial RootRun
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch
open bulksketch.decode.row bulksketch.decode.stages bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

/-- The admitted native state delivered by a successful candidate stage. -/
structure DeflateCandidateHandoff {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) : Prop where
  budgetCap : self.budget.nonzero.val ≤ input.difference.length
  degreeBound : self.degree.val ≤ self.budget.nonzero.val
  hitBound : self.hits.val ≤ self.degree.val
  exactCount : self.roots.count = self.hits
  emptyPending : self.roots.pending = 0#usize
  admitted : WorkspaceAdmission.Admitted (workspaceLengths workspace)
    input.difference.length self.budget.nonzero.val

noncomputable def initialDeflateLocator {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) : Polynomial Field :=
  activeLocator (prefixSlice workspace.bm (input.difference.length + 1)) self.degree

def deflateHits {K : Type} (self : Execution bulksketch.field.Gf64 K) (workspace : RowWorkspace) :
    Slice U64 := prefixSlice workspace.roots self.hits.val

structure DeflateCandidateMeaning {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) : Prop where
  monic : (initialDeflateLocator self input workspace).Monic
  degree : (initialDeflateLocator self input workspace).natDegree = self.degree.val
  split : (initialDeflateLocator self input workspace).Splits
  simple : (initialDeflateLocator self input workspace).roots.Nodup
  nonzeroRoots : ∀ point, (initialDeflateLocator self input workspace).IsRoot point → point ≠ 0
  supplied : ∀ j, j < self.hits.val →
    (initialDeflateLocator self input workspace).IsRoot (toField (deflateHits self workspace)[j]!.bv)
  distinct : ∀ i j, i < j → j < self.hits.val →
    (deflateHits self workspace)[i]! ≠ (deflateHits self workspace)[j]!

private theorem joined_lengths {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (width : Nat) (locator quotient : Slice U64) :
    workspaceLengths (joinedWorkspace (deflateFrame self workspace width) locator quotient) =
      workspaceLengths workspace := by
  simp only [workspaceLengths, joinedWorkspace, deflateFrame, BmEntry.splitBack_length]

private theorem admitted_deflate_bounds {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (input : RowInput) (workspace : RowWorkspace) (handoff : DeflateCandidateHandoff self input workspace) :
    DeflateBounds self input workspace := by
  obtain ⟨budgetCap, degreeBound, hitBound, _, _, admitted⟩ := handoff
  obtain ⟨_, _, _, _, _, _, _, _, bm, _, _, _, _, roots, _, _⟩ := admitted
  change 4 * (input.difference.length + 1) ≤ workspace.bm.length at bm
  change self.budget.nonzero.val ≤ workspace.roots.length at roots
  exact ⟨by omega, degreeBound.trans budgetCap, hitBound, hitBound.trans (degreeBound.trans roots)⟩

theorem residual_simple_split {initial residual : Polynomial Field} (hits : Slice U64)
    (count degree : Nat) (product : initial = rootProduct hits 0 count * residual)
    (monic : initial.Monic) (degreeEq : initial.natDegree = count + degree)
    (split : initial.Splits) (simple : initial.roots.Nodup)
    (nonzeroRoots : ∀ point, initial.IsRoot point → point ≠ 0) :
    residual.Monic ∧ residual.natDegree = degree ∧ residual.Splits ∧ residual.roots.Nodup ∧
      (∀ point, residual.IsRoot point → point ≠ 0) := by
  have divides : residual ∣ initial := ⟨rootProduct hits 0 count, product.trans (mul_comm ..)⟩
  obtain ⟨normalized, exactDegree⟩ :=
    residual_monic_of_degree initial residual hits 0 count degree product monic degreeEq
  refine ⟨normalized, exactDegree, split.of_dvd monic.ne_zero divides,
    Multiset.nodup_of_le (Polynomial.roots.le_of_dvd monic.ne_zero divides) simple, ?_⟩
  intro point root
  apply nonzeroRoots point
  rw [product, Polynomial.IsRoot.def, eval_mul, show residual.eval point = 0 from root, mul_zero]

private theorem product_has_root (hits : Slice U64) (index count j : Nat)
    (inside : index ≤ j ∧ j < index + count) :
    (rootProduct hits index count).IsRoot (toField hits[j]!.bv) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
    rw [rootProduct, Polynomial.IsRoot.def, eval_mul]
    by_cases first : j = index
    · subst j
      rw [eval_add, eval_X, eval_C, ← toField_xor, BitVec.xor_self, show toField (0#64) = 0 from toField_zero, zero_mul]
    · rw [show (rootProduct hits (index + 1) count).eval (toField hits[j]!.bv) = 0
        from ih (index + 1) ⟨by omega, by omega⟩, mul_zero]

theorem residual_excludes_supplied {initial residual : Polynomial Field} (hits : Slice U64) (count : Nat)
    (product : initial = rootProduct hits 0 count * residual)
    (normalized : residual.Monic) (simple : initial.roots.Nodup)
    (j : Nat) (inside : j < count) :
    ¬ residual.IsRoot (toField hits[j]!.bv) := by
  intro root
  have factorMonic := (root_product_monic_of_degree hits 0 count).1
  rw [product, roots_mul (mul_ne_zero factorMonic.ne_zero normalized.ne_zero)] at simple
  have earlier := (mem_roots factorMonic.ne_zero).mpr (product_has_root hits 0 count j ⟨by omega, by omega⟩)
  exact Multiset.disjoint_left.mp (Multiset.disjoint_of_nodup_add simple) earlier
    ((mem_roots normalized.ne_zero).mpr root)

/-- The exact native deflate return initializes the root traversal. The
positive-budget branch carries the pending-factor layout and ready buffers. -/
def ActualNativeDeflateTraversalEntry : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (_mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
    (workspace : RowWorkspace) (meter meter1 : WorkMeter),
    DeflateCandidateHandoff self input workspace →
    DeflateCandidateMeaning self input workspace →
    0 < self.budget.nonzero.val →
    StageCharge.chargeResult meter (deflateCost self.degree) = (.Ok (), meter1) →
    ∃ final : FinalState,
      let capacity := input.difference.length
      let budget := self.budget.nonzero.val
      let width := capacity + 1
      let residual := activeLocator final.locator final.degree
      let updated := finishedRoots self.roots final.degree
      let joined := joinedWorkspace (deflateFrame self workspace width) final.locator final.quotient
      let written := RootSetup.startedWorkspace final.degree joined
      final.index = self.hits.val ∧ final.degree.val + self.hits.val = self.degree.val ∧
      initialDeflateLocator self input workspace = rootProduct (deflateHits self workspace) 0 self.hits.val * residual ∧
      Execution.deflate field kernels self input workspace meter =
        .ok (.Ok (.Ok (some (ClosedLeafAdvance.stageFor updated))), {self with roots := updated}, written, id, meter1) ∧
      Roots.start self.roots final.degree joined = .ok (ClosedLeafAdvance.stageFor updated, updated, written, id) ∧
      updated.pending = 0#usize ∧ updated.count = self.hits ∧ updated.degree = final.degree ∧
      updated.stride.val = final.degree.val + 1 ∧ updated.affine_ready = false ∧
      written.roots = workspace.roots ∧ written.basis.directions = none ∧ written.basis.len = 0#u32 ∧
      WorkspaceAdmission.Admitted (workspaceLengths written) capacity budget ∧
      factorDegreeMass updated written.stack = self.degree.val ∧ factorDegreeMass updated written.stack ≤ budget ∧
      BudgetBuffers written capacity budget ∧
      PendingLayout updated written.stack written.factors.length written.polynomials.length ∧
      (2 ≤ final.degree.val → factorReady updated written) ∧
      (final.degree ≠ 0#usize → activeFactor updated written = residual) ∧
      residual.Monic ∧ residual.natDegree = final.degree.val ∧ residual.Splits ∧ residual.roots.Nodup ∧
      (∀ point, residual.IsRoot point → point ≠ 0) ∧
      (∀ j, j < self.hits.val → ¬ residual.IsRoot (toField (deflateHits self workspace)[j]!.bv))

theorem native_deflate_traversal_entry : ActualNativeDeflateTraversalEntry := by
  intro K field kernels mul self input workspace meter meter1 handoff meaning positive charged
  have bounds := admitted_deflate_bounds self input workspace handoff
  obtain ⟨budgetCap, degreeBound, _, originalCount, emptyPending, originalAdmitted⟩ := handoff
  obtain ⟨originalMonic, originalDegree, originalSplit, originalSimple, originalNonzero, supplied, distinct⟩ := meaning
  have sourceBuffers := budget_buffers_of_admitted workspace input.difference.length self.budget.nonzero.val
    positive originalAdmitted
  have polyRoom : self.degree.val < workspace.polynomials.length := by
    have := sourceBuffers.polynomials
    have := degreeBound
    omega
  obtain ⟨final, finalIndex, degree, locLen, _, product, native⟩ :=
    native_deflate_distinct field kernels mul self input workspace meter meter1 bounds polyRoom charged
      supplied distinct
  let width := input.difference.length + 1
  let joined := joinedWorkspace (deflateFrame self workspace width) final.locator final.quotient
  have admittedJoined : WorkspaceAdmission.Admitted (workspaceLengths joined)
      input.difference.length self.budget.nonzero.val := by
    change WorkspaceAdmission.Admitted (workspaceLengths
      (joinedWorkspace (deflateFrame self workspace width) final.locator final.quotient))
      input.difference.length self.budget.nonzero.val
    rw [joined_lengths]
    exact originalAdmitted
  have exactCount : self.roots.count.val = self.hits.val := by rw [originalCount]
  have mass : self.roots.count.val + final.degree.val ≤ self.budget.nonzero.val := by
    have := degreeBound
    omega
  have start := native_root_traversal_start self.roots final.degree joined input.difference.length
    self.budget.nonzero.val admittedJoined budgetCap emptyPending mass
  dsimp only at start
  obtain ⟨startNormal, pending, count, nextDegree, stride, affineReady, basisEmpty, basisLen,
    admitted, massExact, massBound, active, buffered, ready⟩ := start
  have bmRoom : width ≤ workspace.bm.length := by
    have := sourceBuffers.bm
    omega
  have degreeRoom : final.degree.val < width := by
    have := degreeBound
    have := budgetCap
    omega
  have activeExact (nonzero : final.degree ≠ 0#usize) :
      activeFactor (finishedRoots self.roots final.degree) (RootSetup.startedWorkspace final.degree joined) =
        activeLocator final.locator final.degree := by
    change _ = slicePolynomial (prefixSlice final.locator (final.degree.val + 1))
    rw [finishedRoots, active nonzero]
    exact congrArg slicePolynomial (joined_locator_prefix self workspace width final.locator final.quotient
      (final.degree.val + 1) bmRoom locLen (by omega))
  have fullDegree : (initialDeflateLocator self input workspace).natDegree =
      self.hits.val + final.degree.val := by
    rw [originalDegree]
    omega
  have residual := residual_simple_split (deflateHits self workspace) self.hits.val final.degree.val
    product originalMonic fullDegree originalSplit originalSimple originalNonzero
  have disjoint := residual_excludes_supplied (deflateHits self workspace) self.hits.val product
    residual.1 originalSimple
  obtain ⟨buffers, layout⟩ := buffered positive
  refine ⟨final, finalIndex, degree, product, native, startNormal, pending,
    count.trans originalCount, nextDegree, stride, affineReady, rfl, basisEmpty, basisLen,
    admitted, massExact.trans (by omega), massBound, buffers, layout, ready, activeExact,
    residual.1, residual.2.1, residual.2.2.1, residual.2.2.2.1, residual.2.2.2.2, disjoint⟩

private theorem joined_initial_windows {K : Type} (self : Execution bulksketch.field.Gf64 K)
    (workspace : RowWorkspace) (width : Nat) :
    joinedWorkspace (deflateFrame self workspace width) (prefixSlice workspace.bm width)
      (prefixSlice (BmEntry.tail workspace.bm width) width) = workspace := by
  let tail := BmEntry.tail workspace.bm width
  have restored : restorePrefix tail (prefixSlice tail width) = tail := by
    apply Slice.ext
    simp only [restorePrefix, prefixSlice, Slice.from_val, List.setSlice!, List.take_zero, List.nil_append,
      Nat.sub_zero, Nat.zero_add, List.length_take, min_assoc, min_self]
    rw [List.take_take, min_assoc, min_comm tail.val.length width, ← min_assoc, min_self]
    exact List.take_append_drop ..
  have back : BmEntry.splitBack workspace.bm width (prefixSlice workspace.bm width, tail) = workspace.bm := by
    have sizes : (prefixSlice workspace.bm width).length = min width workspace.bm.length ∧
        tail.length = workspace.bm.length - width :=
      ⟨prefix_length .., BmEntry.tail_length ..⟩
    unfold BmEntry.splitBack
    rw [dite_eq_left sizes]
    apply Slice.ext
    simp only [prefixSlice, tail, BmEntry.tail, Slice.from_val]
    exact List.take_append_drop ..
  unfold joinedWorkspace deflateFrame
  dsimp only
  rw [restored, back]

/-- Zero-budget admission permits an empty polynomial buffer. No root is
consumed and the original start takes its zero-degree path, leaving all
scratch slices intact and resetting just the basis and traversal state. -/
def ActualNativeDeflateZeroBudget : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (_mul : ∀ a b, kernels.ArithmeticInst.mul a b = .ok (mulWord a b))
    (self : Execution bulksketch.field.Gf64 K) (input : RowInput)
    (workspace : RowWorkspace) (meter meter1 : WorkMeter),
    DeflateCandidateHandoff self input workspace →
    self.budget.nonzero.val = 0 →
    StageCharge.chargeResult meter (deflateCost self.degree) = (.Ok (), meter1) →
    let updated := finishedRoots self.roots 0#usize
    let written := {workspace with basis := ⟨none, 0#u32⟩}
    self.hits = 0#usize ∧ self.degree = 0#usize ∧
    Execution.deflate field kernels self input workspace meter =
      .ok (.Ok (.Ok (some .Leaf)), {self with roots := updated}, written, id, meter1) ∧
    Roots.start self.roots 0#usize workspace = .ok (.Leaf, updated, written, id) ∧
    updated.pending = 0#usize ∧ updated.count = 0#usize ∧ updated.degree = 0#usize ∧
    factorDegreeMass updated written.stack = 0 ∧
    WorkspaceAdmission.Admitted (workspaceLengths written) input.difference.length 0

theorem native_deflate_zero_budget : ActualNativeDeflateZeroBudget := by
  intro K field kernels mul self input workspace meter meter1 handoff budgetZero charged
  have bounds := admitted_deflate_bounds self input workspace handoff
  obtain ⟨budgetCap, degreeBound, hitBound, count, empty, admitted⟩ := handoff
  have degreeZero : self.degree = 0#usize := by
    apply UScalar.eq_of_val_eq
    change self.degree.val = 0
    omega
  have hitsZero : self.hits = 0#usize := by
    apply UScalar.eq_of_val_eq
    change self.hits.val = 0
    omega
  have countZero : self.roots.count = 0#usize := count.trans hitsZero
  have admittedZero : WorkspaceAdmission.Admitted (workspaceLengths workspace) input.difference.length 0 := by
    rwa [budgetZero] at admitted
  have source := native_deflate field kernels mul self input workspace meter (deflateCost self.degree)
    (deflate_price self.degree) (fun _ => bounds)
  rw [charged] at source
  obtain ⟨result, trace, exactNative⟩ := source
  let width := input.difference.length + 1
  let locator := prefixSlice workspace.bm width
  let quotient := prefixSlice (BmEntry.tail workspace.bm width) width
  let frame := deflateFrame self workspace width
  have emptyRoots : (prefixSlice workspace.roots self.hits.val).length = 0 := by
    rw [hitsZero, prefix_length]
    rfl
  have ended : result = startOutput frame locator quotient self.degree := by
    cases trace with
    | exhausted _ => rfl
    | rejected => simp_all
    | accepted => simp_all
  have restored : joinedWorkspace frame locator quotient = workspace :=
    joined_initial_windows self workspace width
  have ready := native_root_traversal_start self.roots 0#usize workspace input.difference.length 0
    admittedZero (Nat.zero_le _) empty (by rw [countZero]; decide)
  dsimp only at ready
  obtain ⟨started, pending, hitCount, outDegree, _, _, _, _, admittedAfter, mass, _⟩ := ready
  have normalized : startOutput frame locator quotient self.degree =
      .ok (.Ok (some .Leaf), finishedRoots self.roots 0#usize,
        {workspace with basis := ⟨none, 0#u32⟩}, workspaceParts) := by
    unfold startOutput
    rw [restored, degreeZero, show frame.roots = self.roots from rfl, started, bind_ok]
    rfl
  have exact : Execution.deflate field kernels self input workspace meter =
      .ok (.Ok (.Ok (some .Leaf)), {self with roots := finishedRoots self.roots 0#usize},
        {workspace with basis := ⟨none, 0#u32⟩}, id, meter1) := by
    rw [exactNative, ended, normalized]
    simp only [wrapDeflate, bind_ok]
    dsimp! only
    rfl
  refine ⟨hitsZero, degreeZero, exact, ?_, pending, hitCount.trans countZero, outDegree, ?_, admittedAfter⟩
  · exact started
  · rw [countZero] at mass
    exact mass

#print axioms residual_simple_split
#print axioms native_deflate_traversal_entry
#print axioms native_deflate_zero_budget

end BulksketchBridge.Deflation
