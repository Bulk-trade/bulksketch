import BulksketchBridge.RootNativeClosedLeafVerify
import BulksketchBridge.RootNativeLeafInvariant

namespace BulksketchBridge.ClosedLeaf

open Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr RootRun ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

private theorem tail_preserves_traversal (locator : Polynomial Field) (roots : Roots)
    (workspace : RowWorkspace) (capacity budget offset : Nat) (replacement : Slice U64)
    (invariant : RootTraversalInvariant locator roots workspace capacity budget)
    (separate : roots.degree.val + 1 ≤ offset) (offsetRoom : offset ≤ workspace.polynomials.length) :
    let written := { workspace with polynomials := workspace.polynomials.setSlice! offset replacement.val }
    ∀ count, RootTraversalInvariant locator { roots with solved_count := count } written capacity budget := by
  intro written count
  let after := { roots with solved_count := count }
  have width : written.polynomials.length = workspace.polynomials.length := Slice.setSlice!_length ..
  have lengths : workspaceLengths written = workspaceLengths workspace := by
    simp only [workspaceLengths, written, Slice.setSlice!_length]
  have sameFactor : activeFactor after written = activeFactor roots workspace := by
    unfold activeFactor
    congr 1
    apply Slice.ext
    simp only [after, written, prefixSlice, Slice.from_val, Slice.setSlice!_val, List.setSlice!, List.append_assoc]
    rw [List.take_append_of_le_length (by rw [List.length_take, Nat.min_eq_left offsetRoom]; exact separate),
      List.take_take, Nat.min_eq_left separate]
  have product : activeTraversalProduct after written = locator := by
    unfold activeTraversalProduct traversalProduct liveProduct
    change (if roots.degree.val = 0 then _ else _) = locator
    rw [sameFactor]
    exact invariant.represented
  have layout : PendingLayout after written.stack written.factors.length written.polynomials.length := by
    rw [width]
    exact ⟨invariant.layout.stackRoom, invariant.layout.factorRoom, invariant.layout.polynomialRoom,
      invariant.layout.slots⟩
  exact ⟨budget_buffers_same_lengths workspace written capacity budget invariant.buffers lengths,
    invariant.degreeBudget, layout, product, invariant.mass, invariant.stride, invariant.live,
    invariant.zeroActive, fun positive => sameFactor.symm ▸ invariant.active positive, invariant.pending⟩

/-- The source small-degree solve leaves the active and pending factors
intact. A miss enters reducer preparation, and a hit sets the original
candidate count before factor verification. -/
def ActualNativeClosedLeafSolveTraversal : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace) (stage : Stage)
    (meter paid : WorkMeter) (capacity budget : Nat),
    Cubic.CorrectArithmetic kernels →
    (stage = .LeafThree ∧ roots.degree = 3#usize ∨ stage = .LeafFour ∧ roots.degree = 4#usize) →
    RootTraversalInvariant locator roots workspace capacity budget →
    StageCharge.chargeResult meter (.Ok (leafPrice roots stage)) = (.Ok (), paid) →
    ∃ next after written,
      Roots.run nativeCalls nativeDivRem dictionary kernels roots stage workspace meter =
        .ok (normalReturn next after written paid) ∧
      RootTraversalInvariant locator after written capacity budget ∧
      after.degree = roots.degree ∧ after.pending = roots.pending ∧ after.direction = roots.direction ∧
      written.basis = workspace.basis ∧
      (next = .ReducerPreparation ∨ next = .FactorVerification ∧ after.solved_count = roots.degree) ∧
      traversalRank next after written < traversalRank stage roots workspace

theorem native_closed_leaf_solve_traversal : ActualNativeClosedLeafSolveTraversal := by
  intro K kernels locator roots workspace stage meter paid capacity budget arithmetic branch invariant paidExact
  have degree : roots.degree = 3#usize ∨ roots.degree = 4#usize := branch.imp And.right And.right
  have degreeValues := degree_values roots degree
  have bound := invariant.mass.trans_le invariant.degreeBudget
  unfold factorDegreeMass at bound
  have polys := invariant.buffers.polynomials
  have phase : verifying stage = false := by
    rcases branch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rfl
  have admitted : Admitted roots stage workspace :=
    ⟨degree, by omega, by simp [phase], by simp [phase], by simp [phase]⟩
  have dispatch : Roots.run nativeCalls nativeDivRem dictionary kernels roots stage workspace meter =
      Roots.closed_leaf fieldDictionary kernels roots stage workspace meter := by
    rcases branch with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;>
      exact original_root_run_refines kernels roots _ workspace meter trivial
  have factorLen := factor_length roots workspace degreeValues (by omega)
  have outputLen := region_length workspace.polynomials 11 15 (by omega)
  obtain ⟨⟨solved, replacement⟩, normal, cubic, quartic⟩ := QuarticSolve.solve_refines kernels
    (factorWords roots workspace) (region workspace.polynomials 11 15) arithmetic (by omega) (by omega)
  have solvedCount : ∀ value, solved = some value → value = roots.degree := by
    intro value someValue
    rcases degree with three | four
    · obtain ⟨candidates, _, exactFrame⟩ := cubic (by rw [three] at factorLen; exact factorLen)
      rw [three]
      cases candidates <;> simp [QuarticSolve.expectedFrame, someValue] at exactFrame
      exact exactFrame.1
    · obtain ⟨candidates, _, exactFrame⟩ := quartic (by rw [four] at factorLen; exact factorLen)
      rw [four]
      cases candidates <;> simp [QuarticSolve.expectedFrame, someValue] at exactFrame
      exact exactFrame.1
  have exactRun : Roots.run nativeCalls nativeDivRem dictionary kernels roots stage workspace meter =
      .ok (solveFrame roots workspace paid (solved, replacement)) := by
    rw [dispatch, closed_leaf_refines kernels roots stage workspace meter arithmetic admitted]
    simp only [expected, paidExact, phase, Bool.false_eq_true, ite_false, normal, bind_ok]
    rfl
  let written := { workspace with polynomials := workspace.polynomials.setSlice! 11 replacement.val }
  cases option : solved with
  | none =>
    have safe := tail_preserves_traversal locator roots workspace capacity budget 11 replacement invariant
      (by omega) (by omega) roots.solved_count
    refine ⟨.ReducerPreparation, roots, written, by simpa only [solveFrame, option, written] using exactRun, safe, rfl, rfl, rfl, rfl, Or.inl rfl, ?_⟩
    apply traversal_rank_decreases
    refine Or.inr ⟨rfl, ?_⟩
    rcases branch with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact .fallbackThree ..
    · exact .fallbackFour ..
  | some count =>
    have exactCount := solvedCount count option
    have safe := tail_preserves_traversal locator roots workspace capacity budget 11 replacement invariant
      (by omega) (by omega) count
    refine ⟨.FactorVerification, { roots with solved_count := count }, written, by simpa only [solveFrame, option, written] using exactRun, safe,
      rfl, rfl, rfl, rfl, Or.inr ⟨rfl, exactCount⟩, ?_⟩
    apply traversal_rank_decreases
    refine Or.inr ⟨rfl, ?_⟩
    rcases branch with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact .solveThree ..
    · exact .solveFour ..

/-- The paid source certificate either preserves the traversal for the
reducer or emits the factor and restores the exact pending continuation. -/
def ActualNativeClosedLeafCertificateTraversal : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid : WorkMeter) (capacity budget : Nat),
    Cubic.CorrectArithmetic kernels → (roots.degree = 3#usize ∨ roots.degree = 4#usize) →
    roots.solved_count.val ≤ 4 → RootTraversalInvariant locator roots workspace capacity budget →
    StageCharge.chargeResult meter (.Ok (leafPrice roots .FactorVerification)) = (.Ok (), paid) →
    let (valid, product) := certificateResult roots workspace
    if valid then
      ∃ next after written,
        Roots.run nativeCalls nativeDivRem dictionary kernels roots .FactorVerification workspace meter =
          .ok (normalReturn next after written paid) ∧
        RootLeaf.LeafTraversalOutcome locator roots after workspace written next capacity budget
    else
      let written := checkedWorkspace workspace product
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .FactorVerification workspace meter =
        .ok (normalReturn .ReducerPreparation roots written paid) ∧
      RootTraversalInvariant locator roots written capacity budget ∧
      traversalRank .ReducerPreparation roots written < traversalRank .FactorVerification roots workspace

theorem native_closed_leaf_certificate_traversal : ActualNativeClosedLeafCertificateTraversal := by
  intro K kernels locator roots workspace meter paid capacity budget arithmetic degree count invariant charged
  have degreeValues := degree_values roots degree
  have mass := invariant.mass.trans_le invariant.degreeBudget
  have used := mass
  unfold factorDegreeMass at used
  have polys := invariant.buffers.polynomials
  have rootRoom : roots.count.val + roots.degree.val ≤ workspace.roots.length :=
    (show roots.count.val + roots.degree.val ≤ budget by omega).trans invariant.buffers.roots
  have admitted : Admitted roots .FactorVerification workspace :=
    ⟨degree, by omega, fun _ => by omega, fun _ => count, fun _ _ => rootRoom⟩
  have certified := native_closed_leaf_verify kernels roots workspace meter paid capacity budget
    arithmetic degree count invariant.buffers mass invariant.layout charged
  have dispatch : Roots.run nativeCalls nativeDivRem dictionary kernels roots .FactorVerification workspace meter =
      Roots.closed_leaf fieldDictionary kernels roots .FactorVerification workspace meter :=
    original_root_run_refines kernels roots .FactorVerification workspace meter trivial
  have positive : 0 < roots.degree.val := by omega
  have oldProduct : traversalProduct false roots workspace = locator := by
    simpa only [activeTraversalProduct, Nat.ne_of_gt positive, ite_false] using invariant.represented
  cases cert : certificateResult roots workspace with
  | mk valid product =>
    rw [cert] at certified
    cases valid
    · obtain ⟨ran, _⟩ := certified
      refine ⟨ran, ?_, ?_⟩
      · exact tail_preserves_traversal locator roots workspace capacity budget 15 product invariant
          (by omega) (by omega) roots.solved_count
      · apply traversal_rank_decreases
        exact Or.inr ⟨rfl, .fallbackCertificate ..⟩
    · obtain ⟨_, _, _, next, after, written, ran, outCount, _, layout, productEq, terminal, popped⟩ := certified
      obtain ⟨countedWord, _, emptyRun, popRun⟩ :=
        accepted_advance kernels roots workspace meter paid product arithmetic admitted charged cert
      let counted := { roots with count := countedWord }
      let scratch := acceptedWorkspace roots workspace product
      have scratchLengths : workspaceLengths scratch = workspaceLengths workspace := by
        simp only [scratch, acceptedWorkspace, checkedWorkspace, workspaceLengths, Slice.setSlice!_length]
      have scratchPoly : scratch.polynomials.length = workspace.polynomials.length :=
        congrArg WorkspaceAdmission.Lengths.polynomials scratchLengths
      have scratchLayout : PendingLayout counted scratch.stack scratch.factors.length scratch.polynomials.length := by
        rw [scratchPoly]
        exact ⟨invariant.layout.stackRoom, invariant.layout.factorRoom, invariant.layout.polynomialRoom,
          invariant.layout.slots⟩
      by_cases empty : roots.pending = 0#usize
      · have same := Result.ok_injective (ran.symm.trans (dispatch.trans (emptyRun empty)))
        have rootsEq : after = counted := congrArg (fun frame : LeafReturn => frame.2.1) same
        have workspaceEq : written = scratch := congrArg (fun frame : LeafReturn => frame.2.2.1) same
        have pendingEmpty : after.pending = 0#usize := by rw [rootsEq]; exact empty
        have finalCount : after.count.val = locator.natDegree := by
          rw [outCount]
          simpa only [factorDegreeMass, pendingDegree, empty, show (0#usize).val = 0 from rfl,
            Finset.range_zero, Finset.sum_empty, Nat.add_zero] using invariant.mass
        have finalProduct : emittedProduct after written = locator := by
          simpa only [empty, decide_true, traversalProduct, ite_true] using productEq.trans oldProduct
        exact ⟨next, after, written, ran, outCount, workspaceEq.symm ▸ scratchLengths,
          fun _ => ⟨terminal empty, pendingEmpty, finalCount, finalProduct⟩,
          fun impossible => (impossible empty).elim⟩
      · obtain ⟨frame, bounds, _⟩ := pop_bounds_of_pending_layout counted scratch scratchLayout empty
        let restored := poppedRoots counted scratch frame
        let copied := poppedWorkspace scratch frame
        have same := Result.ok_injective (ran.symm.trans (dispatch.trans (popRun frame bounds)))
        have rootsEq : after = restored := congrArg (fun frame : LeafReturn => frame.2.1) same
        have workspaceEq : written = copied := congrArg (fun frame : LeafReturn => frame.2.2.1) same
        have nextEq : next = stageFor after := by
          rw [rootsEq]
          exact core.result.Result.Ok.inj (core.result.Result.Ok.inj (congrArg (fun frame : LeafReturn => frame.1) same))
        have outWidths : workspaceLengths written = workspaceLengths workspace := by
          rw [workspaceEq]
          simp only [copied, workspaceLengths, poppedWorkspace, restore_length] at scratchLengths ⊢
          exact scratchLengths
        have pendingVal : after.pending.val = roots.pending.val - 1 := by
          rw [rootsEq]
          exact word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
        have degreeVal : after.degree.val = frame.coefficient_len.val - 1 := by
          rw [rootsEq]
          exact word_val _ ((Nat.sub_le ..).trans (bounds.2.2.2.1.trans scratch.polynomials.length_ineq))
        have active : activeFactor after written = pendingFactor workspace frame := by
          rw [rootsEq, workspaceEq]
          exact popped_factor counted scratch frame bounds
        have stride : after.stride = roots.stride := by rw [rootsEq]; rfl
        have stack : written.stack = workspace.stack := by rw [workspaceEq]; rfl
        have factors : written.factors = workspace.factors := by rw [workspaceEq]; rfl
        have frameRead : workspace.stack.val[roots.pending.val - 1]? = some frame := bounds.2.1
        obtain ⟨_, _, _, afterMass, rank⟩ := popped empty
        have sameProduct : traversalProduct false after written = traversalProduct false roots workspace := by
          simpa only [empty, decide_false] using productEq
        have hasPending : 0 < roots.pending.val :=
          Nat.pos_of_ne_zero (fun value => empty (UScalar.eq_of_val_eq value))
        have safe := traversal_invariant_after_pop locator roots after workspace written capacity budget frame
          invariant hasPending frameRead degreeVal pendingVal stride (by omega)
          outWidths stack factors active layout afterMass sameProduct
        exact ⟨next, after, written, ran, outCount, outWidths, fun impossible => (empty impossible).elim,
          fun _ => ⟨frame, frameRead, nextEq, pendingVal, degreeVal, active, safe, rank⟩⟩

#print axioms native_closed_leaf_certificate_traversal

#print axioms native_closed_leaf_solve_traversal

end BulksketchBridge.ClosedLeaf
