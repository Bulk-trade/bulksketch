import BulksketchBridge.RootLeafWords
import BulksketchBridge.RootTraversalPotential
import BulksketchBridge.RootEmissionProduct
import BulksketchBridge.DenseReducerAlgebra
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootPendingBudget
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.RootLeaf

open Aeneas Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RootRun ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem leaf_paid_model (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (words : Slice U64)
    (charged : bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Ok (), paid))
    (selected : leafCandidates roots.degree.val workspace.polynomials = .Ok words)
    (nonzero : 0#u64 ∉ words.val) :
    expectedLeaf roots workspace meter = leafResume roots workspace words paid := by
  have chargedModel : expectedLeaf roots workspace meter = (do
      let (reply, finalMeter) ← bulksketch.decode.roots.charge meter (.Leaf roots.degree)
      match reply with
      | .Err reason => .ok (.Err reason, roots, workspace, id, finalMeter)
      | .Ok () =>
        match leafCandidates roots.degree.val workspace.polynomials with
        | .Err reason => .ok (.Ok (.Err reason), roots, workspace, id, finalMeter)
        | .Ok candidates =>
          if 0#u64 ∈ candidates.val then .ok (.Ok (.Err .InvalidLocator), roots, workspace, id, finalMeter)
          else leafResume roots workspace candidates finalMeter) := by
    rw [ClosedLeafAdvance.charge_refines]
    unfold expectedLeaf
    simp only [Aeneas.Std.bind_assoc, bind_ok]
    rfl
  rw [chargedModel, charged, bind_ok]
  dsimp! only
  rw [selected]
  dsimp! only
  exact ite_eq_right nonzero

/-- Paid degree-zero, -one and -two leaf emission. The actual dispatcher
    appends exactly the complete root set, preserves the old root words,
    and either enters verification or restores the exact pending factor. -/
def ActualNativeLeafComplete : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (capacity budget : Nat),
    DirectTwo.CorrectArithmetic kernels → roots.degree.val ≤ 2 →
    BudgetBuffers workspace capacity budget → factorDegreeMass roots workspace.stack ≤ budget →
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Ok (), paid) →
    (0 < roots.degree.val →
      workspace.polynomials[roots.degree.val]! = 1#u64 ∧
      (activeFactor roots workspace).Splits ∧ (activeFactor roots workspace).roots.Nodup ∧
      ¬ (activeFactor roots workspace).IsRoot 0) →
    ∃ (words : Slice U64) (stage : Stage) (after : Roots) (written : RowWorkspace),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
        .ok (.Ok (.Ok stage), after, written, id, paid) ∧
      words.length = roots.degree.val ∧ words.val.Nodup ∧ 0#u64 ∉ words.val ∧
      after.count.val = roots.count.val + roots.degree.val ∧
      written.roots = workspace.roots.setSlice! roots.count.val words.val ∧
      PendingLayout after written.stack written.factors.length written.polynomials.length ∧
      (0 < roots.degree.val → ∀ point, (activeFactor roots workspace).IsRoot point ↔
        ∃ word ∈ words.val, point = toField word.bv) ∧
      (0 < roots.degree.val → traversalProduct (decide (roots.pending = 0#usize)) after written =
        traversalProduct false roots workspace) ∧
      (roots.pending = 0#usize → stage = .Verification) ∧
      (roots.pending ≠ 0#usize → ∃ frame, workspace.stack.val[roots.pending.val - 1]? = some frame ∧
        activeFactor after written = pendingFactor workspace frame ∧
        factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack ∧
        (0 < roots.degree.val → traversalPotential after written.stack < traversalPotential roots workspace.stack))

theorem native_leaf_complete : ActualNativeLeafComplete := by
  intro K kernels roots workspace meter paid capacity budget arithmetic degreeBound sized mass layout charged admitted
  have massLe := mass
  unfold factorDegreeMass at massLe
  have poly := sized.polynomials
  have rootRoom : roots.count.val + roots.degree.val ≤ workspace.roots.length := by have := sized.roots; omega
  have bounds : LeafBounds roots workspace := ⟨degreeBound, by omega, rootRoom⟩
  obtain ⟨words, selected, wordLen, nonzero, unique, complete⟩ :=
    leaf_candidates_complete roots workspace degreeBound (fun positive => ⟨by omega, admitted positive⟩)
  let counted := { roots with count := usizeWord (roots.count.val + roots.degree.val) }
  let emitted := { workspace with roots := workspace.roots.setSlice! roots.count.val words.val }
  have countRoom : roots.count.val + roots.degree.val ≤ Usize.max := rootRoom.trans workspace.roots.length_ineq
  have countValue : counted.count.val = roots.count.val + roots.degree.val := word_val _ countRoom
  have countedLayout : PendingLayout counted emitted.stack emitted.factors.length emitted.polynomials.length := by
    refine ⟨layout.stackRoom, layout.factorRoom, layout.polynomialRoom, ?_⟩
    intro slot live
    exact layout.slots slot live
  have source : Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
      leafResume roots workspace words paid := by
    rw [original_root_run_refines kernels roots .Leaf workspace meter trivial]
    change Roots.leaf DirectTwo.fieldDictionary kernels roots workspace meter = _
    rw [root_leaf_refines kernels roots workspace meter arithmetic bounds,
      leaf_paid_model roots workspace meter paid words charged selected nonzero]
  have factorProduct (positive : 0 < roots.degree.val) :
      activeFactor roots workspace = rootsProduct words.val := by
    obtain ⟨lead, split, simple, _⟩ := admitted positive
    let coefficients := prefixSlice workspace.polynomials (roots.degree.val + 1)
    have coeffWidth : coefficients.length = roots.degree.val + 1 := by
      rw [RebuiltLfsr.prefix_length, Nat.min_eq_left (by omega)]
    have coeffLead : coefficients[roots.degree.val]! = 1#u64 := by
      simp only [coefficients, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
        List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt (Nat.lt_succ_self roots.degree.val)]
      simpa only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using lead
    have monic := (DenseReducerAlgebra.modulus_monic coefficients roots.degree.val coeffWidth coeffLead).1
    exact factor_from_emitted_roots (activeFactor roots workspace) words.val monic split simple unique (complete positive)
  have emittedRoom : roots.count.val + words.val.length ≤ workspace.roots.length := by
    change roots.count.val + words.length ≤ workspace.roots.length
    rwa [wordLen]
  have countWords : counted.count.val = roots.count.val + words.val.length := by
    change counted.count.val = roots.count.val + words.length
    rw [countValue, wordLen]
  by_cases empty : roots.pending = 0#usize
  · have advanced := advance_empty_refines counted emitted empty
    have executed : Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
        .ok (.Ok (.Ok .Verification), counted, emitted, id, paid) := by
      rw [source]
      unfold leafResume
      dsimp only
      rw [advanced]
      simp only [bind_ok]
      rfl
    have emptyProduct : pendingProduct workspace roots.pending.val = (1 : Polynomial Field) := by
      simp only [pendingProduct, empty, show (0#usize).val = 0 from rfl,
        Finset.range_zero, Finset.prod_empty]
    have product (positive : 0 < roots.degree.val) :
        traversalProduct true counted emitted = traversalProduct false roots workspace :=
      emission_preserves_traversal_product roots counted workspace emitted words.val true emittedRoom
        countWords rfl (factorProduct positive) (by exact emptyProduct)
    exact ⟨words, .Verification, counted, emitted, executed, wordLen, unique, nonzero, countValue, rfl,
      countedLayout, complete, fun positive => by simpa only [empty, decide_true] using product positive,
      fun _ => rfl, fun impossible => (impossible empty).elim⟩
  · obtain ⟨frame, active, _⟩ := pop_bounds_of_pending_layout counted emitted countedLayout empty
    let after := poppedRoots counted emitted frame
    let written := poppedWorkspace emitted frame
    have advanced := advance_pop_refines counted emitted frame active
    have executed : Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
        .ok (.Ok (.Ok (stageFor after)), after, written, id, paid) := by
      rw [source]
      unfold leafResume
      dsimp only
      rw [advanced]
      simp only [bind_ok]
      rfl
    have pendingFactorization : pendingProduct workspace roots.pending.val = liveProduct after written :=
      popped_pending_product counted emitted frame active
    have afterCount : after.count.val = roots.count.val + words.val.length := countWords
    have product (positive : 0 < roots.degree.val) :
        traversalProduct false after written = traversalProduct false roots workspace :=
      emission_preserves_traversal_product roots after workspace written words.val false emittedRoom
        afterCount rfl (factorProduct positive) (by exact pendingFactorization)
    refine ⟨words, stageFor after, after, written, executed, wordLen, unique, nonzero,
      countValue, rfl, popped_pending_layout counted emitted frame countedLayout, complete,
      fun positive => by simpa only [empty, decide_false] using product positive,
      fun impossible => (empty impossible).elim, ?_⟩
    intro _
    have oldPop : PopBounds roots workspace frame := active
    have massPreserved := popped_degree_mass roots workspace frame oldPop countRoom
    have potential := popped_potential_decreases roots workspace frame oldPop
    exact ⟨frame, active.2.1, popped_factor counted emitted frame active, massPreserved, potential⟩

/-- A zero-budget row reaches verification through the original leaf
without reading coefficient storage or adding a root. -/
def ActualNativeZeroLeaf : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter),
    DirectTwo.CorrectArithmetic kernels →
    roots.degree = 0#usize → roots.count = 0#usize → roots.pending = 0#usize →
    bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Ok (), paid) →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
      .ok (.Ok (.Ok .Verification), roots, workspace, id, paid)

theorem native_zero_leaf : ActualNativeZeroLeaf := by
  intro K kernels roots workspace meter paid arithmetic zero count pending charged
  have degreeZero : roots.degree.val = 0 := by rw [zero]; rfl
  have countZero : roots.count.val = 0 := by rw [count]; rfl
  have bounds : LeafBounds roots workspace := ⟨by omega, by omega, by omega⟩
  have selected : leafCandidates roots.degree.val workspace.polynomials = .Ok emptyRoots := by
    rw [degreeZero]
    rfl
  have noRoot : 0#u64 ∉ emptyRoots.val := by simp [emptyRoots]
  rw [original_root_run_refines kernels roots .Leaf workspace meter trivial]
  change Roots.leaf DirectTwo.fieldDictionary kernels roots workspace meter = _
  rw [root_leaf_refines kernels roots workspace meter arithmetic bounds,
    leaf_paid_model roots workspace meter paid emptyRoots charged selected noRoot]
  have zeroCount : usizeWord (roots.count.val + roots.degree.val) = roots.count := by
    apply UScalar.eq_of_val_eq
    rw [countZero, degreeZero, Nat.zero_add, word_val _ (Nat.zero_le _)]
  have sameRoots : workspace.roots.setSlice! roots.count.val emptyRoots.val = workspace.roots := by
    apply Slice.ext
    simp only [countZero, emptyRoots, Slice.from_val, Slice.setSlice!_val, List.setSlice!,
      List.take_zero, List.nil_append, List.length_nil, Nat.zero_min, Nat.zero_add, List.drop_zero]
  unfold leafResume
  dsimp only
  rw [zeroCount, sameRoots]
  change (do
    let (stage, after, written, back) ← Roots.advance roots workspace
    Result.ok ((.Ok (.Ok stage) : LeafReply), after, written, back, paid)) = _
  rw [advance_empty_refines roots workspace pending]
  simp only [Bind.bind, bind_ok]

#print axioms native_leaf_complete

end BulksketchBridge.RootLeaf
