import BulksketchBridge.AffineEnumerationSuffix
import BulksketchBridge.AffineEnumerationCompleteness
import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootEnumerate
import BulksketchBridge.RootTraversalPotential

namespace BulksketchBridge.RootEnumerate

open Aeneas Aeneas.Std Algebra.Gf64 Polynomial DenseCoefficient RebuiltLfsr SliceKernels
open AffineEnumerate AffineSubspaceAlgebra AffineSubspaces RootRun ClosedLeafAdvance
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1900000

private theorem prefix_word (words : Slice U64) (count index : Nat) (active : index < count) :
    (prefixSlice words count)[index]! = words[index]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_take_of_lt active]

private theorem emitted_prefix (original candidates : Slice U64) (start degree : Nat)
    (room : start ≤ original.length) (width : candidates.length = original.length - start) :
    (original.setSlice! start candidates.val).val.take (start + degree) =
      original.val.take start ++ candidates.val.take degree := by
  have fit : start ≤ original.val.length := room
  have exactWidth : candidates.val.length = original.val.length - start := width
  simp only [Slice.setSlice!_val, List.setSlice!, Nat.min_eq_left exactWidth.le, List.take_length]
  rw [List.drop_eq_nil_of_le (by omega), List.append_nil, List.take_append, List.length_take,
    Nat.min_eq_left fit, Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (by rw [List.length_take, Nat.min_eq_left fit]; omega)]

private theorem emitted_window (original candidates : Slice U64) (start degree : Nat)
    (room : start + degree ≤ original.length) (width : candidates.length = original.length - start)
    (preserved : candidates.val.drop degree = original.val.drop (start + degree)) :
    original.setSlice! start candidates.val = original.setSlice! start (candidates.val.take degree) := by
  have fits : start + degree ≤ original.val.length := room
  have exactWidth : candidates.val.length = original.val.length - start := width
  have emittedRoom : degree ≤ candidates.val.length := by omega
  apply Slice.ext
  calc
    (original.setSlice! start candidates.val).val = original.val.take start ++ candidates.val := by
      simp only [Slice.setSlice!_val, List.setSlice!, Nat.min_eq_left exactWidth.le, List.take_length,
        List.drop_eq_nil_of_le (by omega : original.val.length ≤ start + candidates.val.length), List.append_nil]
    _ = original.val.take start ++ (candidates.val.take degree ++ original.val.drop (start + degree)) := by
      rw [← preserved, List.take_append_drop]
    _ = (original.setSlice! start (candidates.val.take degree)).val := by
      simp only [Slice.setSlice!_val, List.setSlice!, List.length_take, Nat.min_eq_left emittedRoom,
        Nat.min_eq_left (by omega : degree ≤ original.val.length - start), List.take_take, min_self,
        List.append_assoc]

/-- The paid original affine enumerator appends the active factor's full
root set exactly once. The source wrapper either enters verification or
restores the exact pending frame, with its degree accounting preserved. -/
def ActualNativeAffineEnumerationComplete : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter paid : WorkMeter) (capacity budget : Nat)
    (directions : Array U64 64#usize),
    HornerLaw kernels →
    BudgetBuffers workspace capacity budget → factorDegreeMass roots workspace.stack ≤ budget →
    PendingLayout roots workspace.stack workspace.factors.length workspace.polynomials.length →
    workspace.basis.directions = some directions →
    roots.affine_rank.val < System.Platform.numBits →
    workspace.polynomials[roots.degree.val]! = 1#u64 →
    (activeFactor roots workspace).Splits → (activeFactor roots workspace).roots.Nodup →
    ¬ (activeFactor roots workspace).IsRoot 0 →
    let basis := prefixSlice directions.to_slice roots.affine_rank.val
    IndependentDirections basis →
    (∀ point, (activeFactor roots workspace).IsRoot point →
      point ∈ coset (toField roots.affine_base.bv) (prefixDirections basis basis.length)) →
    charge meter (chargedOperation roots) = .ok (.Ok (), paid) →
    ∃ (words : List U64) (stage : Stage) (after : Roots) (written : RowWorkspace),
      Roots.run nativeCalls nativeDivRem dictionary kernels roots .AffineEnumeration workspace meter =
        .ok (.Ok (.Ok stage), after, written, id, paid) ∧
      StageCharge.chargeResult meter (enumerationCost roots.degree roots.affine_rank) = (.Ok (), paid) ∧
      words.length = roots.degree.val ∧ words.Nodup ∧ 0#u64 ∉ words ∧
      (∀ point, (activeFactor roots workspace).IsRoot point ↔
        ∃ word ∈ words, point = toField word.bv) ∧
      after.count.val = roots.count.val + roots.degree.val ∧
      written.roots = workspace.roots.setSlice! roots.count.val words ∧
      written.roots.val.take after.count.val = workspace.roots.val.take roots.count.val ++ words ∧
      workspaceLengths written = workspaceLengths workspace ∧
      PendingLayout after written.stack written.factors.length written.polynomials.length ∧
      (roots.pending = 0#usize → stage = .Verification ∧ after.count.val = factorDegreeMass roots workspace.stack) ∧
      (roots.pending ≠ 0#usize → ∃ frame, workspace.stack.val[roots.pending.val - 1]? = some frame ∧
        stage = stageFor after ∧
        after = poppedRoots {roots with count := usizeWord (roots.count.val + roots.degree.val)} workspace frame ∧
        activeFactor after written = pendingFactor workspace frame ∧
        factorDegreeMass after written.stack = factorDegreeMass roots workspace.stack ∧
        (0 < roots.degree.val → traversalPotential after written.stack < traversalPotential roots workspace.stack))

theorem native_affine_enumeration_complete : ActualNativeAffineEnumerationComplete := by
  intro K kernels roots workspace meter paid capacity budget directions horner sized mass layout directionsEq
    rank lead split simple nonzero
  dsimp only
  intro independent cosetContains paidSource
  have used := mass
  unfold factorDegreeMass at used
  have rootRoom : roots.count.val + roots.degree.val ≤ workspace.roots.length := by have := sized.roots; omega
  have polyRoom : roots.degree.val < workspace.polynomials.length := by have := sized.polynomials; omega
  have workRoom : 2 ≤ workspace.bm.length := by have := sized.bm; omega
  have rankRoom : roots.affine_rank.val ≤ 64 := by have := System.Platform.numBits_le; omega
  let polynomial := prefixSlice workspace.polynomials (roots.degree.val + 1)
  let basis := prefixSlice directions.to_slice roots.affine_rank.val
  let suffix := BmEntry.tail workspace.roots roots.count.val
  have polyLen : polynomial.length = roots.degree.val + 1 := by
    change (prefixSlice workspace.polynomials (roots.degree.val + 1)).length = _
    rw [prefix_length, Nat.min_eq_left (by omega)]
  have basisLen : basis.length = roots.affine_rank.val := by
    change (prefixSlice directions.to_slice roots.affine_rank.val).length = _
    rw [prefix_length, Array.length_to_slice]
    exact Nat.min_eq_left rankRoom
  have suffixLen : suffix.length = workspace.roots.length - roots.count.val := BmEntry.tail_length ..
  have highest : polynomial[polynomial.length - 1]! = 1#u64 := by
    rw [polyLen, Nat.add_sub_cancel]
    change (prefixSlice workspace.polynomials (roots.degree.val + 1))[roots.degree.val]! = _
    rw [prefix_word _ _ _ (by omega), lead]
  obtain ⟨candidates, scratch, inner, candidateLen, scratchLen, meanings⟩ :=
    native_enumeration_complete kernels horner polynomial roots.affine_base basis suffix workspace.bm
      (by omega) (by omega) workRoom (by rwa [basisLen]) highest nonzero split simple independent cosetContains
  have foundEq : usizeWord (polynomial.length - 1) = roots.degree := by
    apply UScalar.eq_of_val_eq
    rw [polyLen, Nat.add_sub_cancel, word_val _ (by scalar_tac)]
  rw [foundEq] at inner
  have keepsTail := native_enumerate_keeps_suffix kernels horner polynomial roots.affine_base basis suffix
    workspace.bm (by omega) (by omega) workRoom (by rwa [basisLen]) (.Ok roots.degree)
    candidates scratch inner
  rw [polyLen, Nat.add_sub_cancel] at keepsTail
  have oldTail : suffix.val.drop roots.degree.val =
      workspace.roots.val.drop (roots.count.val + roots.degree.val) := by
    change (BmEntry.tail workspace.roots roots.count.val).val.drop roots.degree.val = _
    rw [BmEntry.tail, Slice.from_val, List.drop_drop]
  have innerLaw : CandidateLaw bulksketch.decode.affine.enumerate dictionary kernels roots workspace directions := by
    refine ⟨.Ok roots.degree, candidates, scratch, inner, candidateLen.trans suffixLen, scratchLen, ?_⟩
    intro found same
    cases same
    omega
  have prepared : Ready bulksketch.decode.affine.enumerate dictionary kernels roots workspace := by
    refine ⟨polyRoom, rankRoom, by omega, ?_, directions, directionsEq, innerLaw⟩
    intro active
    obtain ⟨frame, bounds, _⟩ := pop_bounds_of_pending_layout roots workspace layout active
    exact ⟨frame, bounds⟩
  obtain ⟨reply, finalMeter, paidModel, chargeReturn, wrapper⟩ := enumerate_affine_refines
    bulksketch.decode.affine.enumerate dictionary kernels roots workspace meter (fun _ _ => prepared)
  have samePayment := Result.ok_injective (chargeReturn.symm.trans paidSource)
  have replyEq : reply = .Ok () := congrArg Prod.fst samePayment
  have meterEq : finalMeter = paid := congrArg Prod.snd samePayment
  subst reply
  subst finalMeter
  obtain ⟨directions', reply, actualCandidates, actualScratch, directionsSet, called, _, _, branch⟩ := wrapper
  have sameDirections := Option.some.inj (directionsSet.symm.trans directionsEq)
  subst directions'
  have sameInner := Result.ok_injective (called.symm.trans inner)
  have replyEq : reply = .Ok roots.degree := congrArg Prod.fst sameInner
  have candidatesEq : actualCandidates = candidates := congrArg (fun output => output.2.1) sameInner
  have scratchEq : actualScratch = scratch := congrArg (fun output => output.2.2) sameInner
  subst reply
  subst actualCandidates
  subst actualScratch
  obtain ⟨count, countValue, _, resumed⟩ := branch
  have countRoom : roots.count.val + roots.degree.val ≤ Usize.max := rootRoom.trans workspace.roots.length_ineq
  have countExact : count = usizeWord (roots.count.val + roots.degree.val) :=
    UScalar.eq_of_val_eq (countValue.trans (word_val _ countRoom).symm)
  let counted := { roots with count := count }
  let emitted := updatedWorkspace roots workspace candidates scratch
  let words := candidates.val.take roots.degree.val
  have outLen : words.length = roots.degree.val := by
    change (candidates.val.take roots.degree.val).length = _
    rw [List.length_take, Nat.min_eq_left (by change _ ≤ candidates.length; omega)]
  have exactWords : (words.map fun word => toField word.bv).Nodup ∧
      ∀ point, point ∈ words.map (fun word => toField word.bv) ↔ (activeFactor roots workspace).IsRoot point := by
    have size : polynomial.length - 1 = roots.degree.val := by omega
    simp only [size] at meanings
    exact meanings
  have distinct := List.Nodup.of_map _ exactWords.1
  have allRoots (point : Field) : (activeFactor roots workspace).IsRoot point ↔
      ∃ word ∈ words, point = toField word.bv := by
    rw [← exactWords.2 point, List.mem_map]
    exact exists_congr (fun word => and_congr_right (fun _ => eq_comm))
  have zeroFree : 0#u64 ∉ words := by
    intro hasZero
    exact nonzero ((allRoots 0).mpr ⟨0#u64, hasZero, toField_zero.symm⟩)
  have exactWrite : emitted.roots = workspace.roots.setSlice! roots.count.val words :=
    emitted_window workspace.roots candidates roots.count.val roots.degree.val rootRoom
      (candidateLen.trans suffixLen) (keepsTail.trans oldTail)
  have prefixWritten : emitted.roots.val.take counted.count.val =
      workspace.roots.val.take roots.count.val ++ words := by
    rw [show counted.count.val = count.val from rfl, countValue]
    exact emitted_prefix workspace.roots candidates roots.count.val roots.degree.val (by omega)
      (candidateLen.trans suffixLen)
  have emittedLengths : workspaceLengths emitted = workspaceLengths workspace := by
    simp only [emitted, updatedWorkspace, workspaceLengths, scratchLen, Slice.setSlice!_length]
  have countedLayout : PendingLayout counted emitted.stack emitted.factors.length emitted.polynomials.length := by
    refine ⟨layout.stackRoom, layout.factorRoom, layout.polynomialRoom, ?_⟩
    intro slot live
    exact layout.slots slot live
  rw [original_root_run_refines kernels roots .AffineEnumeration workspace meter trivial]
  simp only [RootRun.expected]
  by_cases empty : roots.pending = 0#usize
  · rw [ite_eq_left empty] at resumed
    refine ⟨words, .Verification, counted, emitted, resumed, paidModel, outLen, distinct, zeroFree,
      allRoots, countValue, exactWrite, prefixWritten, emittedLengths, countedLayout, ?_, fun impossible => (impossible empty).elim⟩
    intro _
    simp only [factorDegreeMass, pendingDegree, empty, show (0#usize).val = 0 from rfl,
      Finset.range_zero, Finset.sum_empty, Nat.add_zero]
    exact ⟨trivial, countValue⟩
  · rw [ite_eq_right empty] at resumed
    obtain ⟨frame, popBounds, ran⟩ := resumed
    let after := poppedRoots counted emitted frame
    let written := poppedWorkspace emitted frame
    have oldPop : PopBounds roots workspace frame := popBounds
    have oldMass := popped_degree_mass roots workspace frame oldPop countRoom
    have oldPotential := popped_potential_decreases roots workspace frame oldPop
    have restoredLengths : workspaceLengths written = workspaceLengths workspace := by
      change workspaceLengths (poppedWorkspace emitted frame) = _
      simp only [workspaceLengths, poppedWorkspace, restore_length] at emittedLengths ⊢
      exact emittedLengths
    refine ⟨words, stageFor after, after, written, ran, paidModel, outLen, distinct, zeroFree,
      allRoots, countValue, exactWrite, prefixWritten, restoredLengths, popped_pending_layout counted emitted frame countedLayout,
      fun impossible => (empty impossible).elim, ?_⟩
    intro _
    refine ⟨frame, popBounds.2.1, rfl, ?_, popped_factor counted emitted frame popBounds, ?_, ?_⟩
    · unfold after counted
      rw [countExact]
      rfl
    · change factorDegreeMass (poppedRoots counted emitted frame) (poppedWorkspace emitted frame).stack = _
      unfold counted
      rw [countExact]
      exact oldMass
    · intro positive
      exact oldPotential positive

#print axioms native_affine_enumeration_complete

end BulksketchBridge.RootEnumerate
