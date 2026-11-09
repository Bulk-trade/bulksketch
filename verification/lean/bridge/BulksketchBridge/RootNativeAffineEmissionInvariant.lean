import BulksketchBridge.RootNativeLeafInvariant
import BulksketchBridge.RootNativeAffineEnumerationComplete

namespace BulksketchBridge.RootEnumerate

open Aeneas Aeneas.Std Result Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr SliceKernels
open AffineEnumerate AffineSubspaceAlgebra AffineSubspaces RootRun ClosedLeafAdvance
open RootLeaf ExecutionDriver
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.decode.stages bulksketch.decode.row

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

private theorem enumeration_keeps_pending_storage {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (horner : HornerLaw kernels) (roots after : Roots) (workspace written : RowWorkspace) (stage : Stage)
    (meter paid : WorkMeter) (directions : Array U64 64#usize)
    (polyRoom : roots.degree.val < workspace.polynomials.length)
    (rootRoom : roots.count.val + roots.degree.val ≤ workspace.roots.length)
    (workRoom : 2 ≤ workspace.bm.length) (rank : roots.affine_rank.val < System.Platform.numBits)
    (directionsEq : workspace.basis.directions = some directions)
    (layout : PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length)
    (charged : charge meter (chargedOperation roots) = .ok (.Ok (), paid))
    (native : Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineEnumeration workspace meter =
      .ok (.Ok (.Ok stage), after, written, id, paid)) :
    written.stack = workspace.stack ∧ written.factors = workspace.factors ∧
      (roots.pending = 0#usize → after.pending = 0#usize) := by
  have prepared : Ready bulksketch.decode.affine.enumerate dictionary kernels roots workspace := by
    refine ⟨polyRoom, by have := System.Platform.numBits_le; omega, by omega, ?_, directions, directionsEq, ?_⟩
    · intro live
      obtain ⟨frame, bounds, _⟩ := pop_bounds_of_pending_layout roots workspace layout live
      exact ⟨frame, bounds⟩
    · exact original_candidate_law kernels horner roots workspace directions polyRoom rootRoom rank workRoom
  obtain ⟨reply, finalMeter, _, paidNormal, wrapper⟩ := enumerate_affine_refines
    bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter (fun _ _ => prepared)
  have samePayment := Result.ok_injective (paidNormal.symm.trans charged)
  have replyEq : reply = .Ok () := congrArg Prod.fst samePayment
  have meterEq : finalMeter = paid := congrArg Prod.snd samePayment
  subst reply
  subst finalMeter
  obtain ⟨_, answer, candidates, scratch, _, _, _, _, wrapper⟩ := wrapper
  rw [original_root_run_refines kernels roots .AffineEnumeration workspace meter trivial] at native
  change Roots.enumerate_affine bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter =
    .ok (.Ok (.Ok stage), after, written, id, paid) at native
  cases answer with
  | Err error =>
    have same := Result.ok_injective (native.symm.trans wrapper)
    have reply := congrArg (fun f : RootRun.Frame => f.1) same
    cases core.result.Result.Ok.inj reply
  | Ok count =>
    obtain ⟨nextCount, _, _, resumed⟩ := wrapper
    by_cases empty : roots.pending = 0#usize
    · rw [ite_eq_left empty] at resumed
      have same := Result.ok_injective (native.symm.trans resumed)
      have state := congrArg (fun f : RootRun.Frame => f.2.1) same
      have out := congrArg (fun f : RootRun.Frame => f.2.2.1) same
      change after = {roots with count := nextCount} at state
      change written = updatedWorkspace roots workspace candidates scratch at out
      rw [state, out]
      exact ⟨rfl, rfl, fun _ => empty⟩
    · rw [ite_eq_right empty] at resumed
      obtain ⟨frame, _, resumed⟩ := resumed
      have same := Result.ok_injective (native.symm.trans resumed)
      have out := congrArg (fun f : RootRun.Frame => f.2.2.1) same
      change written = poppedWorkspace (updatedWorkspace roots workspace candidates scratch) frame at out
      rw [out]
      exact ⟨rfl, rfl, fun impossible => (empty impossible).elim⟩

/-- Paid affine enumeration is an emission step for the same traversal
invariant. It either restores the exact pending factor and saves degree
mass, or hands the whole emitted product to verification. -/
def ActualNativeAffineEmissionInvariant : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (locator : Polynomial Field) (roots : Roots) (workspace : RowWorkspace)
    (meter paid : WorkMeter) (capacity budget : Nat) (directions : Array U64 64#usize),
    RootTraversalInvariant locator roots workspace capacity budget →
    0 < roots.degree.val → HornerLaw kernels → workspace.basis.directions = some directions →
    roots.affine_rank.val < System.Platform.numBits →
    let basis := prefixSlice directions.to_slice roots.affine_rank.val
    IndependentDirections basis →
    (∀ point, (activeFactor roots workspace).IsRoot point →
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis basis.length)) →
    charge meter (chargedOperation roots) = .ok (.Ok (), paid) →
    ∃ (stage : Stage) (after : Roots) (written : RowWorkspace),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineEnumeration workspace meter =
        .ok (.Ok (.Ok stage), after, written, id, paid) ∧
      LeafTraversalOutcome locator roots after workspace written stage capacity budget

theorem native_affine_emission_invariant : ActualNativeAffineEmissionInvariant := by
  intro K kernels locator roots workspace meter paid capacity budget directions invariant positive horner directionEq rank
  dsimp only
  intro independent contains charged
  have mass := invariant.mass.trans_le invariant.degreeBudget
  have used := mass
  unfold factorDegreeMass at used
  have rootRoom : roots.count.val + roots.degree.val ≤ workspace.roots.length := by
    have := invariant.buffers.roots
    omega
  have polyRoom : roots.degree.val < workspace.polynomials.length := by
    have := invariant.buffers.polynomials
    omega
  have workRoom : 2 ≤ workspace.bm.length := by have := invariant.buffers.bm; omega
  obtain ⟨monic, degree, split, simple, noZero⟩ := invariant.active positive
  have coeff : (activeFactor roots workspace).coeff roots.degree.val = 1 := by
    rw [← degree, coeff_natDegree, monic.leadingCoeff]
  have lead : workspace.polynomials[roots.degree.val]! = 1#u64 := by
    change (slicePolynomial (prefixSlice workspace.polynomials (roots.degree.val + 1))).coeff roots.degree.val = 1 at coeff
    have width : (prefixSlice workspace.polynomials (roots.degree.val + 1)).length = roots.degree.val + 1 :=
      (prefix_length ..).trans (Nat.min_eq_left (by omega))
    rw [slicePolynomial_coeff, ite_eq_left (by omega)] at coeff
    have read : (prefixSlice workspace.polynomials (roots.degree.val + 1))[roots.degree.val]! =
        workspace.polynomials[roots.degree.val]! := by
      simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
        List.getElem?_take_of_lt (Nat.lt_succ_self _)]
    rw [read] at coeff
    apply U64.bv_eq_imp_eq
    exact toField_injective (coeff.trans toField_one.symm)
  obtain ⟨_, stage, after, written, source, _, _, _, _, _, count, _, _, widths, layout, product, terminal, popped⟩ :=
    native_affine_enumeration_complete kernels roots workspace meter paid capacity budget directions
      horner invariant.buffers mass invariant.layout directionEq rank lead split simple
      (fun root => noZero 0 root rfl) independent contains charged
  obtain ⟨stack, factors, emptyAfter⟩ := enumeration_keeps_pending_storage kernels horner roots after workspace
    written stage meter paid directions polyRoom rootRoom workRoom rank directionEq invariant.layout charged source
  have oldProduct : traversalProduct false roots workspace = locator := by
    simpa only [activeTraversalProduct, Nat.ne_of_gt positive, ite_false] using invariant.represented
  refine ⟨stage, after, written, source, count, widths, ?_, ?_⟩
  · intro empty
    obtain ⟨nextStage, exactCount⟩ := terminal empty
    have emitted : emittedProduct after written = locator := by
      simpa only [empty, decide_true, traversalProduct, ite_true] using product.trans oldProduct
    exact ⟨nextStage, emptyAfter empty, exactCount.trans invariant.mass, emitted⟩
  · intro live
    obtain ⟨frame, top, nextStage, restored, active, outMass, potential⟩ := popped live
    obtain ⟨actual, pop, _⟩ := pop_bounds_of_pending_layout roots workspace invariant.layout live
    have same := Option.some.inj (pop.2.1.symm.trans top)
    subst actual
    have pendingVal : after.pending.val = roots.pending.val - 1 := by
      rw [restored]
      exact word_val _ ((Nat.sub_le ..).trans (by scalar_tac))
    have outDegree : after.degree.val = frame.coefficient_len.val - 1 := by
      rw [restored]
      exact word_val _ ((Nat.sub_le ..).trans (pop.2.2.2.1.trans workspace.polynomials.length_ineq))
    have stride : after.stride = roots.stride := by rw [restored]; rfl
    have preserved : traversalProduct false after written = traversalProduct false roots workspace := by
      simpa only [live, decide_false] using product
    have hasPending : 0 < roots.pending.val := Nat.pos_of_ne_zero (fun value => live (UScalar.eq_of_val_eq value))
    have safe := traversal_invariant_after_pop locator roots after workspace written capacity budget frame
      invariant hasPending top outDegree pendingVal stride (by omega)
      widths stack factors active layout outMass preserved
    exact ⟨frame, top, nextStage, pendingVal, outDegree, active, safe, potential positive⟩

theorem affine_emission_destination_progress {K : Type} (locator : Polynomial Field)
    (before after : RootDrainState K) (next : Stage) (capacity budget : Nat)
    (step : LeafTraversalOutcome locator before.execution.roots after.execution.roots before.workspace
      after.workspace next capacity budget) :
    RootDestinationProgress before after .AffineEnumeration next := by
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

private theorem affine_charge_rejection {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (error : DecodeError)
    (charged : charge meter (chargedOperation roots) = .ok (.Err error, paid)) :
    Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineEnumeration workspace meter =
      .ok (.Err error, roots, workspace, id, paid) := by
  have ready : ∀ paid, charge meter (chargedOperation roots) = .ok (.Ok (), paid) →
      Ready bulksketch.decode.affine.enumerate dictionary kernels roots workspace := by
    intro final impossible
    have different := congrArg Prod.fst (Result.ok_injective (charged.symm.trans impossible))
    cases different
  obtain ⟨reply, final, _, chargeNormal, wrapper⟩ := enumerate_affine_refines
    bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter ready
  have same := Result.ok_injective (chargeNormal.symm.trans charged)
  have replyEq : reply = .Err error := congrArg Prod.fst same
  have meterEq : final = paid := congrArg Prod.snd same
  subst reply
  subst final
  rw [original_root_run_refines kernels roots .AffineEnumeration workspace meter trivial]
  exact wrapper

/-- The original affine enumeration wrapper contributes a ranked native
step on either charge branch. Basis and coset premises are used only
when the charge allows enumeration. -/
def ActualNativeAffineEmissionRankedStep : Prop :=
  ∀ (canonicalize : ExecutionDriverRuntime.Canonicalize) {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (input : RowInput) (admitted : RootDrainState K → Prop) (before : RootDrainState K)
    (locator : Polynomial Field) (capacity budget : Nat),
    before.execution.state = .Running .AffineEnumeration → before.execution.degree_probe = none →
    RootTraversalInvariant locator before.execution.roots before.workspace capacity budget →
    (∀ (stage : Stage) (after : Roots) (written : RowWorkspace) (paid : WorkMeter),
      LeafTraversalOutcome locator before.execution.roots after before.workspace written stage capacity budget →
      admitted ⟨{before.execution with state := .Running stage, roots := after}, written, paid⟩) →
    ∀ (reply : core.result.Result Unit DecodeError) (paid : WorkMeter),
      charge before.meter (chargedOperation before.execution.roots) = .ok (reply, paid) →
      (reply = .Ok () →
        0 < before.execution.roots.degree.val ∧ HornerLaw kernels ∧
        before.execution.roots.affine_rank.val < System.Platform.numBits ∧
        ∃ directions : Array U64 64#usize, before.workspace.basis.directions = some directions ∧
          let basis := prefixSlice directions.to_slice before.execution.roots.affine_rank.val
          IndependentDirections basis ∧
          (∀ point, (activeFactor before.execution.roots before.workspace).IsRoot point →
            point ∈ coset (toField before.execution.roots.affine_base.bv)
              (prefixDirections basis basis.length))) →
      ExecutionFinish.RankedDriverStep (nativeDrainRuntime canonicalize) RootSetup.gf64Dictionary kernels input
        admitted rootTailRank before

theorem native_affine_emission_ranked_step : ActualNativeAffineEmissionRankedStep := by
  intro canonicalize K kernels input admitted before locator capacity budget state probe invariant
    advance reply paid charged ready
  cases reply with
  | Err error =>
    have rejected := affine_charge_rejection kernels before.execution.roots before.workspace before.meter paid error charged
    have source := native_root_charge_error_latched canonicalize kernels input before .AffineEnumeration error paid
      state probe rfl rejected
    exact ⟨.Err error, ⟨{before.execution with state := .Error error}, before.workspace, paid⟩,
      id, source, trivial⟩
  | Ok success =>
    cases success
    obtain ⟨positive, horner, rank, directions, directionEq, independent, contains⟩ := ready rfl
    obtain ⟨stage, roots, written, source, outcome⟩ :=
      native_affine_emission_invariant kernels locator before.execution.roots before.workspace before.meter paid
        capacity budget directions invariant positive horner directionEq rank independent contains charged
    apply ranked_step_of_native_root_return canonicalize kernels input admitted before .AffineEnumeration (.Ok (.Ok stage))
      roots written id paid state probe rfl source
    intro next reply
    have equal : stage = next := core.result.Result.Ok.inj (core.result.Result.Ok.inj reply)
    subst next
    let after : RootDrainState K := ⟨{before.execution with state := .Running stage, roots := roots}, written, paid⟩
    exact ⟨advance stage roots written paid outcome,
      affine_emission_destination_progress locator before after stage capacity budget outcome⟩

#print axioms native_affine_emission_invariant
#print axioms affine_emission_destination_progress
#print axioms native_affine_emission_ranked_step

end BulksketchBridge.RootEnumerate
