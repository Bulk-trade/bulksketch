import BulksketchBridge.RootPopInvariant
import BulksketchBridge.RankedRootDrainAdapter
import BulksketchBridge.RootNativeLeafComplete

namespace BulksketchBridge.RootLeaf

open Aeneas Aeneas.Std Algebra.Gf64 Polynomial SliceKernels DenseCoefficient RebuiltLfsr RootRun ClosedLeafAdvance
open ExecutionDriver
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages bulksketch.decode.row

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem expected_leaf_by_charge (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter) :
    expectedLeaf roots workspace meter = (do
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

private theorem paid_leaf_resume {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (words : Slice U64)
    (arithmetic : DirectTwo.CorrectArithmetic kernels) (bounds : LeafBounds roots workspace)
    (charged : bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Ok (), paid))
    (selected : leafCandidates roots.degree.val workspace.polynomials = .Ok words)
    (nonzero : 0#u64 ∉ words.val) :
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
      leafResume roots workspace words paid := by
  rw [original_root_run_refines kernels roots .Leaf workspace meter trivial]
  change Roots.leaf DirectTwo.fieldDictionary kernels roots workspace meter = _
  rw [root_leaf_refines kernels roots workspace meter arithmetic bounds]
  rw [expected_leaf_by_charge, charged, bind_ok]
  dsimp! only
  rw [selected]
  dsimp! only
  exact ite_eq_right nonzero

/-- A native zero-degree leaf emits nothing, even when earlier steps
have already written roots. No coefficient buffer is needed. -/
def ActualNativeEmptyLeaf : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter),
    DirectTwo.CorrectArithmetic kernels →
    roots.degree = 0#usize → roots.pending = 0#usize → roots.count.val ≤ workspace.roots.length →
    bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Ok (), paid) →
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
      .ok (.Ok (.Ok .Verification), roots, workspace, id, paid)

theorem native_empty_leaf : ActualNativeEmptyLeaf := by
  intro K kernels roots workspace meter paid arithmetic zero pending count charged
  have degreeZero : roots.degree.val = 0 := by rw [zero]; rfl
  have bounds : LeafBounds roots workspace := ⟨by omega, by omega, by omega⟩
  have selected : leafCandidates roots.degree.val workspace.polynomials = .Ok emptyRoots := by
    rw [degreeZero]
    rfl
  rw [paid_leaf_resume kernels roots workspace meter paid emptyRoots arithmetic bounds charged selected
    (by simp [emptyRoots])]
  have sameCount : usizeWord (roots.count.val + roots.degree.val) = roots.count := by
    apply UScalar.eq_of_val_eq
    rw [degreeZero, Nat.add_zero, word_val _ (count.trans workspace.roots.length_ineq)]
  have sameSlice : workspace.roots.setSlice! roots.count.val emptyRoots.val = workspace.roots := by
    apply Slice.ext
    simp only [emptyRoots, Slice.from_val, Slice.setSlice!_val, List.setSlice!, List.length_nil,
      Nat.zero_min, List.take_zero, List.append_nil, Nat.add_zero, List.take_append_drop]
  unfold leafResume
  dsimp only
  rw [sameCount, sameSlice]
  change (do
    let (stage, after, written, back) ← Roots.advance roots workspace
    Result.ok ((.Ok (.Ok stage) : LeafReply), after, written, back, paid)) = _
  rw [advance_empty_refines roots workspace pending]
  simp only [Bind.bind, bind_ok]

private theorem leaf_inputs_from_invariant (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (capacity budget : Nat)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget) (positive : 0 < roots.degree.val) :
    workspace.polynomials[roots.degree.val]! = 1#u64 ∧
      (activeFactor roots workspace).Splits ∧ (activeFactor roots workspace).roots.Nodup ∧
      ¬ (activeFactor roots workspace).IsRoot 0 := by
  obtain ⟨monic, degree, split, simple, nonzero⟩ := invariant.active positive
  have coefficient : (activeFactor roots workspace).coeff roots.degree.val = 1 := by
    rw [← degree, coeff_natDegree, monic.leadingCoeff]
  let polynomial := prefixSlice workspace.polynomials (roots.degree.val + 1)
  have length : polynomial.length = roots.degree.val + 1 := by
    have polyRoom := invariant.buffers.polynomials
    have degreeRoom := invariant.mass.trans_le invariant.degreeBudget
    unfold factorDegreeMass at degreeRoom
    change (prefixSlice workspace.polynomials (roots.degree.val + 1)).length = _
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have top : polynomial[roots.degree.val]! = workspace.polynomials[roots.degree.val]! := by
    simp only [polynomial, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
      List.getElem?_take_of_lt (Nat.lt_succ_self _)]
  change (slicePolynomial polynomial).coeff roots.degree.val = 1 at coefficient
  rw [slicePolynomial_coeff, ite_eq_left (by omega), top] at coefficient
  refine ⟨?_, split, simple, fun root => nonzero 0 root rfl⟩
  apply U64.bv_eq_imp_eq
  exact toField_injective (coefficient.trans toField_one.symm)

def LeafTraversalOutcome (locator : Polynomial Field) (roots after : Roots)
    (workspace written : RowWorkspace) (stage : Stage) (capacity budget : Nat) : Prop :=
  after.count.val = roots.count.val + roots.degree.val ∧
  workspaceLengths written = workspaceLengths workspace ∧
  (roots.pending = 0#usize →
    stage = .Verification ∧ after.pending = 0#usize ∧ after.count.val = locator.natDegree ∧
      emittedProduct after written = locator) ∧
  (roots.pending ≠ 0#usize → ∃ frame,
    workspace.stack.val[roots.pending.val - 1]? = some frame ∧ stage = stageFor after ∧
    after.pending.val = roots.pending.val - 1 ∧ after.degree.val = frame.coefficient_len.val - 1 ∧
    activeFactor after written = pendingFactor workspace frame ∧
    RootTraversalInvariant locator after written capacity budget ∧
    traversalPotential after written.stack < traversalPotential roots workspace.stack)

/-- Paid ordinary leaf preserves the unified invariant after a real pop,
or transfers its complete emitted polynomial and count to verification. -/
def ActualNativeLeafTraversalStep : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter)
    (capacity budget : Nat),
    DirectTwo.CorrectArithmetic kernels → roots.degree.val ≤ 2 →
    RootTraversalInvariant locator roots workspace capacity budget →
    bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Ok (), paid) →
    ∃ (stage : Stage) (after : Roots) (written : RowWorkspace),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
        .ok (.Ok (.Ok stage), after, written, id, paid) ∧
      LeafTraversalOutcome locator roots after workspace written stage capacity budget

theorem native_leaf_traversal_step : ActualNativeLeafTraversalStep := by
  intro K kernels locator roots workspace meter paid capacity budget arithmetic degreeBound invariant charged
  have mass := invariant.mass.trans_le invariant.degreeBudget
  have used := mass
  unfold factorDegreeMass at used
  have rootRoom : roots.count.val + roots.degree.val ≤ workspace.roots.length := by
    have := invariant.buffers.roots
    omega
  have polyRoom : roots.degree.val < workspace.polynomials.length := by
    have := invariant.buffers.polynomials
    omega
  have bounds : LeafBounds roots workspace := ⟨degreeBound, polyRoom.le, rootRoom⟩
  have ready := leaf_inputs_from_invariant locator roots workspace capacity budget invariant
  have countFits : roots.count.val + roots.degree.val ≤ Usize.max := rootRoom.trans workspace.roots.length_ineq
  have original := invariant.represented
  by_cases zero : roots.degree.val = 0
  · have zeroWord : roots.degree = 0#usize := UScalar.eq_of_val_eq zero
    have empty := invariant.zeroActive zero
    have ran := native_empty_leaf kernels roots workspace meter paid arithmetic zeroWord empty (by omega) charged
    have emitted : emittedProduct roots workspace = locator := by
      simpa only [activeTraversalProduct, zero, ite_true, pendingProduct, empty,
        show (0#usize).val = 0 from rfl, Finset.range_zero, Finset.prod_empty, mul_one] using original
    have count : roots.count.val = locator.natDegree := by
      simpa only [factorDegreeMass, zero, pendingDegree, empty, show (0#usize).val = 0 from rfl,
        Finset.range_zero, Finset.sum_empty, Nat.add_zero] using invariant.mass
    exact ⟨.Verification, roots, workspace, ran, by omega, rfl,
      fun _ => ⟨rfl, empty, count, emitted⟩, fun impossible => (impossible empty).elim⟩
  · have positive : 0 < roots.degree.val := Nat.pos_of_ne_zero zero
    obtain ⟨_, stage, after, written, ran, _, _, _, count, _, layout, _, product, terminal, _⟩ :=
      native_leaf_complete kernels roots workspace meter paid capacity budget arithmetic degreeBound
        invariant.buffers mass invariant.layout charged ready
    obtain ⟨words, selected, _, nonzero, _, _⟩ :=
      leaf_candidates_complete roots workspace degreeBound (fun positive => ⟨polyRoom, ready positive⟩)
    have modeled := paid_leaf_resume kernels roots workspace meter paid words arithmetic bounds charged selected nonzero
    let counted := {roots with count := usizeWord (roots.count.val + roots.degree.val)}
    let emitted := {workspace with roots := workspace.roots.setSlice! roots.count.val words.val}
    have lengths : workspaceLengths emitted = workspaceLengths workspace := by
      simp only [emitted, workspaceLengths, Slice.setSlice!_length]
    have oldProduct : traversalProduct false roots workspace = locator := by
      simpa only [activeTraversalProduct, zero, ite_false] using original
    by_cases empty : roots.pending = 0#usize
    · have modeledNormal : leafResume roots workspace words paid =
        .ok (.Ok (.Ok .Verification), counted, emitted, id, paid) := by
        unfold leafResume
        dsimp only
        rw [advance_empty_refines counted emitted empty, bind_ok]
        rfl
      have same := Result.ok_injective (ran.symm.trans (modeled.trans modeledNormal))
      have sameRoots : after = counted := congrArg (fun frame : LeafFrame => frame.2.1) same
      have sameWorkspace : written = emitted := congrArg (fun frame : LeafFrame => frame.2.2.1) same
      have nextEmpty : after.pending = 0#usize := by rw [sameRoots]; exact empty
      have countMass : after.count.val = locator.natDegree := by
        have exactMass := invariant.mass
        rw [count]
        simpa only [factorDegreeMass, pendingDegree, empty, show (0#usize).val = 0 from rfl,
          Finset.range_zero, Finset.sum_empty, Nat.add_zero] using exactMass
      have finalProduct : emittedProduct after written = locator := by
        have proof := (product positive).trans oldProduct
        simpa only [empty, decide_true, traversalProduct, ite_true] using proof
      exact ⟨stage, after, written, ran, count, sameWorkspace ▸ lengths,
        fun _ => ⟨terminal empty, nextEmpty, countMass, finalProduct⟩,
        fun impossible => (impossible empty).elim⟩
    · obtain ⟨frame, pop, _⟩ := pop_bounds_of_pending_layout roots workspace invariant.layout empty
      have updatedPop : PopBounds counted emitted frame := pop
      let restored := poppedRoots counted emitted frame
      let copied := poppedWorkspace emitted frame
      have modeledPop : leafResume roots workspace words paid =
        .ok (.Ok (.Ok (stageFor restored)), restored, copied, id, paid) := by
        unfold leafResume
        dsimp only
        rw [advance_pop_refines counted emitted frame updatedPop, bind_ok]
        rfl
      have same := Result.ok_injective (ran.symm.trans (modeled.trans modeledPop))
      have sameRoots : after = restored := congrArg (fun frame : LeafFrame => frame.2.1) same
      have sameWorkspace : written = copied := congrArg (fun frame : LeafFrame => frame.2.2.1) same
      have nextStage : stage = stageFor after := by
        rw [sameRoots]
        have reply := congrArg (fun frame : LeafFrame => frame.1) same
        exact core.result.Result.Ok.inj (core.result.Result.Ok.inj reply)
      have outLengths : workspaceLengths written = workspaceLengths workspace := by
        rw [sameWorkspace]
        change workspaceLengths (poppedWorkspace emitted frame) = _
        simp only [workspaceLengths, poppedWorkspace, restore_length] at lengths ⊢
        exact lengths
      have pendingVal : after.pending.val = roots.pending.val - 1 := by
        rw [sameRoots]
        exact word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
      have outDegree : after.degree.val = frame.coefficient_len.val - 1 := by
        rw [sameRoots]
        exact word_val _ ((Nat.sub_le ..).trans (pop.2.2.2.1.trans workspace.polynomials.length_ineq))
      have stride : after.stride = roots.stride := by rw [sameRoots]; rfl
      have stack : written.stack = workspace.stack := by rw [sameWorkspace]; rfl
      have factors : written.factors = workspace.factors := by rw [sameWorkspace]; rfl
      have outFactor : activeFactor after written = pendingFactor workspace frame := by
        rw [sameRoots, sameWorkspace]
        exact popped_factor counted emitted frame updatedPop
      have outMass : factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack := by
        rw [sameRoots, sameWorkspace]
        exact popped_degree_mass roots workspace frame pop countFits
      have rank : traversalPotential after written.stack < traversalPotential roots workspace.stack := by
        rw [sameRoots, sameWorkspace]
        exact popped_potential_decreases roots workspace frame pop positive
      have unchangedProduct : traversalProduct false after written = traversalProduct false roots workspace := by
        simpa only [empty, decide_false] using product positive
      have hasPending : 0 < roots.pending.val := Nat.pos_of_ne_zero (fun value => empty (UScalar.eq_of_val_eq value))
      have safe := traversal_invariant_after_pop locator roots after workspace written capacity budget frame
        invariant hasPending pop.2.1 outDegree pendingVal stride (by omega)
        outLengths stack factors outFactor layout outMass unchangedProduct
      exact ⟨stage, after, written, ran, count, outLengths, fun impossible => (empty impossible).elim,
        fun _ => ⟨frame, pop.2.1, nextStage, pendingVal, outDegree, outFactor, safe, rank⟩⟩

theorem leaf_destination_progress {K : Type} (locator : Polynomial Field)
    (before after : RootDrainState K) (next : Stage) (capacity budget : Nat)
    (step : LeafTraversalOutcome locator before.execution.roots after.execution.roots before.workspace
      after.workspace next capacity budget) :
    RootDestinationProgress before after .Leaf next := by
  obtain ⟨_, _, terminal, continues⟩ := step
  by_cases empty : before.execution.roots.pending = 0#usize
  · exact .inl (terminal empty).1
  · obtain ⟨_, _, nextStage, _, _, _, _, potential⟩ := continues empty
    refine .inr ⟨?_, .inl potential⟩
    rw [nextStage]
    unfold stageFor
    split
    · rfl
    · split
      · rfl
      · split <;> rfl

private theorem leaf_charge_rejection {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (error : DecodeError)
    (arithmetic : DirectTwo.CorrectArithmetic kernels) (bounds : LeafBounds roots workspace)
    (charged : bulksketch.decode.roots.charge meter (.Leaf roots.degree) = .ok (.Err error, paid)) :
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .Leaf workspace meter =
      .ok (.Err error, roots, workspace, id, paid) := by
  rw [original_root_run_refines kernels roots .Leaf workspace meter trivial]
  change Roots.leaf DirectTwo.fieldDictionary kernels roots workspace meter = _
  rw [root_leaf_refines kernels roots workspace meter arithmetic bounds, expected_leaf_by_charge, charged, bind_ok]
  rfl

/-- The ordinary Leaf source handler contributes one exact step to the
ranked native driver, for both paid emission and charge rejection. The
destination's stage-specific admission is supplied by the caller. -/
def ActualNativeLeafRankedStep : Prop :=
  ∀ (canonicalize : ExecutionDriverRuntime.Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) (admitted : RootDrainState K → Prop) (before : RootDrainState K)
    (locator : Polynomial Field) (capacity budget : Nat),
    before.execution.state = .Running .Leaf → before.execution.degree_probe = none →
    DirectTwo.CorrectArithmetic kernels → before.execution.roots.degree.val ≤ 2 →
    RootTraversalInvariant locator before.execution.roots before.workspace capacity budget →
    (∀ (stage : Stage) (after : Roots) (written : RowWorkspace) (paid : WorkMeter),
      LeafTraversalOutcome locator before.execution.roots after before.workspace written stage capacity budget →
      admitted ⟨{before.execution with state := .Running stage, roots := after}, written, paid⟩) →
    ∀ (reply : core.result.Result Unit DecodeError) (paid : WorkMeter),
      bulksketch.decode.roots.charge before.meter (.Leaf before.execution.roots.degree) = .ok (reply, paid) →
      ExecutionFinish.RankedDriverStep (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
        admitted rootTailRank before

theorem native_leaf_ranked_step : ActualNativeLeafRankedStep := by
  intro canonicalize K kernels input admitted before locator capacity budget state probe arithmetic degree
    invariant advance reply paid charge
  cases reply with
  | Err error =>
    have used := invariant.mass.trans_le invariant.degreeBudget
    unfold factorDegreeMass at used
    have poly := invariant.buffers.polynomials
    have roots := invariant.buffers.roots
    have bounds : LeafBounds before.execution.roots before.workspace := ⟨degree, by omega, by omega⟩
    have rejected := leaf_charge_rejection kernels before.execution.roots before.workspace before.meter
      paid error arithmetic bounds charge
    have source := native_root_charge_error_latched canonicalize kernels input before .Leaf error paid
      state probe rfl rejected
    exact ⟨.Err error, ⟨{before.execution with state := .Error error}, before.workspace, paid⟩,
      id, source, trivial⟩
  | Ok success =>
    cases success
    obtain ⟨stage, roots, written, source, outcome⟩ :=
      native_leaf_traversal_step kernels locator before.execution.roots before.workspace before.meter paid
        capacity budget arithmetic degree invariant charge
    apply ranked_step_of_native_root_return canonicalize kernels input admitted before .Leaf (.Ok (.Ok stage))
      roots written id paid state probe rfl source
    intro next reply
    have equal : stage = next := core.result.Result.Ok.inj (core.result.Result.Ok.inj reply)
    subst next
    let after : RootDrainState K := ⟨{before.execution with state := .Running stage, roots := roots}, written, paid⟩
    exact ⟨advance stage roots written paid outcome,
      leaf_destination_progress locator before after stage capacity budget outcome⟩

#print axioms native_empty_leaf
#print axioms native_leaf_traversal_step
#print axioms leaf_destination_progress
#print axioms native_leaf_ranked_step

end BulksketchBridge.RootLeaf
