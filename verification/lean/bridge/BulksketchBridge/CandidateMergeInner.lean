import Arithmetic.CandidateMergeGenerated
import BulksketchBridge.CandidateCompactNative
import Mathlib.Data.List.Sort

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.sketch.candidates bulksketch.sketch.shape
open ClosedLeafAdvance (usizeWord word_val)

abbrev MergeIter := core.slice.iter.IterMut U64
abbrev MergeBack := MergeIter → MergeIter

def writeSelected (position : Nat) (word : U64) (later : MergeIter) : MergeIter :=
  { later with slice := later.slice.setAtNat position word }

def takeLeft (buckets : Nat) (ids : Slice U64) (middle stop left right : Usize) : Prop :=
  left.val < middle.val ∧ (right = stop ∨ bucketKey buckets ids[left.val]! ≤ bucketKey buckets ids[right.val]!)

instance (buckets : Nat) (ids : Slice U64) (middle stop left right : Usize) :
    Decidable (takeLeft buckets ids middle stop left right) := by
  unfold takeLeft
  infer_instance

private theorem lex_key (buckets : Nat) (left right : U64) :
    bucketKey buckets left ≤ bucketKey buckets right ↔
      left.val % buckets < right.val % buckets ∨
        left.val % buckets = right.val % buckets ∧ left.val ≤ right.val := by
  have leftFits : left.val < 2 ^ 64 := left.hBounds
  have rightFits : right.val < 2 ^ 64 := right.hBounds
  unfold bucketKey
  change left.val % buckets * 18446744073709551616 + left.val ≤
      right.val % buckets * 18446744073709551616 + right.val ↔ _
  change left.val < 18446744073709551616 at leftFits
  change right.val < 18446744073709551616 at rightFits
  omega

private theorem bucket_call {F : Type} (field : bulksketch.field.BinaryField F)
    (shape : SketchShape F) (id : U64) (positive : 0 < shape.capacities.length) :
    ∃ bucket : Usize,
      normalize.closure.Insts.CoreOpsFunctionFnTupleU64PairUsizeU64.call field shape id =
        .ok (bucket, id) ∧ bucket.val = id.val % shape.capacities.length := by
  obtain ⟨bucket, route, val, _⟩ := native_candidate_bucket field shape id positive
  exact ⟨bucket, by simp only [normalize.closure.Insts.CoreOpsFunctionFnTupleU64PairUsizeU64.call,
    route, bind_ok], val⟩

private theorem pair_call (buckets : Nat) (left right : U64) (leftBucket rightBucket : Usize)
    (leftVal : leftBucket.val = left.val % buckets) (rightVal : rightBucket.val = right.val % buckets) :
    CandidateMergeRuntime.pairLE core.cmp.PartialOrdUsize core.cmp.PartialOrdU64
      (leftBucket, left) (rightBucket, right) =
        .ok (decide (bucketKey buckets left ≤ bucketKey buckets right)) := by
  simp only [CandidateMergeRuntime.pairLE, leftVal, rightVal, lex_key]

private theorem advance_word (word : Usize) (safe : word.val + 1 ≤ Usize.max) :
    (word + 1#usize : Result Usize) = .ok (usizeWord (word.val + 1)) := by
  have one : (1#usize).val = 1 := Usize.ofNatCore_val_eq _
  obtain ⟨next, call, val⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := word) (y := 1#usize) (by rw [one]; exact safe))
  rw [one] at val
  rw [call]
  exact congrArg Result.ok (UScalar.eq_of_val_eq (val.trans (word_val _ safe).symm))

/-- The native innermost merge step chooses the stable lexicographic
minimum and binds its exact backward write to the current iterator slot. -/
theorem native_merge_step {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (ids : Slice U64) (middle stop left right : Usize) (iter : MergeIter) (back : MergeBack)
    (positive : 0 < shape.capacities.length)
    (leftRoom : left.val ≤ middle.val) (middleRoom : middle.val ≤ right.val)
    (rightRoom : right.val ≤ stop.val) (inputRoom : stop.val ≤ ids.length)
    (live : iter.i < iter.slice.length)
    (remaining : iter.slice.length - iter.i = (middle.val - left.val) + (stop.val - right.val)) :
    normalize_loop0_loop0_loop0.body field shape ids middle stop iter back left right =
      .ok (if takeLeft shape.capacities.length ids middle stop left right then
        .cont ({ iter with i := iter.i + 1 }, fun later => back (writeSelected iter.i ids[left.val]! later),
          usizeWord (left.val + 1), right)
      else
        .cont ({ iter with i := iter.i + 1 }, fun later => back (writeSelected iter.i ids[right.val]! later),
          left, usizeWord (right.val + 1))) := by
  have active : iter.i < iter.slice.len.val := by rwa [Slice.len_val]
  have next : core.slice.iter.IteratorIterMut.next iter =
      .ok (some (iter.slice[iter.i]'live), { iter with i := iter.i + 1 },
        fun (later : MergeIter) (replacement : Option U64) => match replacement with
          | none => later
          | some word => writeSelected iter.i word later) := by
    unfold core.slice.iter.IteratorIterMut.next
    rw [dite_eq_left active]
    dsimp only
    apply congrArg Result.ok
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · rfl
      · funext later replacement
        cases replacement <;> rfl
  simp only [normalize_loop0_loop0_loop0.body, next, bind_ok]
  dsimp! only
  have max : ids.length ≤ Usize.max := ids.length_ineq
  by_cases leftActive : left.val < middle.val
  · have leftRead := DenseDivRem.read_normal ids left (by omega)
    have leftNext := advance_word left (by omega)
    by_cases rightEnd : right = stop
    · have take : takeLeft shape.capacities.length ids middle stop left right :=
        ⟨leftActive, Or.inl rightEnd⟩
      rw [ite_eq_left take]
      simp only [UScalar.lt_equiv, leftActive, rightEnd, ite_true, leftRead, leftNext, bind_ok]
    · have rightActive : right.val < stop.val := by
        by_contra! exhausted
        apply rightEnd
        exact UScalar.eq_of_val_eq (by omega)
      have rightRead := DenseDivRem.read_normal ids right (by omega)
      have rightNext := advance_word right (by omega)
      obtain ⟨bLeft, pLeft, vLeft⟩ := bucket_call field shape ids[left.val]! positive
      obtain ⟨bRight, pRight, vRight⟩ := bucket_call field shape ids[right.val]! positive
      have comparison := pair_call shape.capacities.length ids[left.val]! ids[right.val]! bLeft bRight vLeft vRight
      simp only [UScalar.lt_equiv, leftActive, ite_true, rightEnd, ite_false, leftRead, pLeft, rightRead,
        pRight, comparison, bind_ok, decide_eq_true_eq, takeLeft, true_and, false_or]
      by_cases smaller : bucketKey shape.capacities.length ids[left.val]! ≤
          bucketKey shape.capacities.length ids[right.val]!
      · simp only [smaller, ite_true, leftNext, bind_ok]
      · simp only [smaller, ite_false, rightNext, bind_ok]
  · have rightActive : right.val < stop.val := by omega
    have rightRead := DenseDivRem.read_normal ids right (by omega)
    have rightNext := advance_word right (by omega)
    simp only [UScalar.lt_equiv, leftActive, ite_false, rightRead, rightNext, bind_ok,
      takeLeft, false_and]

def keyCompare (buckets : Nat) (a b : U64) : Bool :=
  decide (bucketKey buckets a ≤ bucketKey buckets b)

def mergeSelection (buckets : Nat) (ids : Slice U64) (middle stop left right : Nat) : List U64 :=
  List.merge (ids.val.slice left middle) (ids.val.slice right stop) (keyCompare buckets)

def writeBackList : Nat → List U64 → MergeBack
  | _, [] => id
  | position, word :: rest => fun later =>
    writeSelected position word (writeBackList (position + 1) rest later)

private theorem slice_head (ids : Slice U64) (lo hi : Nat)
    (live : lo < hi) (fit : hi ≤ ids.length) :
    ids.val.slice lo hi = ids[lo]! :: ids.val.slice (lo + 1) hi := by
  have inside : lo < ids.val.length := live.trans_le fit
  have drop : ids.val.drop lo = ids[lo]! :: ids.val.drop (lo + 1) := by
    rw [List.drop_eq_getElem_cons inside, Slice.getElem!_Nat_eq,
      List.Inhabited_getElem_eq_getElem! _ _ inside]
  unfold List.slice
  rw [show hi - lo = hi - (lo + 1) + 1 by omega, drop, List.take_succ_cons]

private theorem slice_empty (ids : Slice U64) (position : Nat) :
    ids.val.slice position position = [] := by simp [List.slice]

private theorem selection_left (buckets : Nat) (ids : Slice U64) (middle stop left right : Usize)
    (middleRoom : middle.val ≤ right.val) (rightRoom : right.val ≤ stop.val)
    (fits : stop.val ≤ ids.length) (take : takeLeft buckets ids middle stop left right) :
    mergeSelection buckets ids middle.val stop.val left.val right.val =
      ids[left.val]! :: mergeSelection buckets ids middle.val stop.val (left.val + 1) right.val := by
  have prefixCall := slice_head ids left.val middle.val take.1 (by omega)
  unfold mergeSelection
  rw [prefixCall]
  rcases take.2 with endRight | keyOrder
  · rw [endRight, slice_empty, List.merge_right, List.merge_right]
  · by_cases endRight : right = stop
    · rw [endRight, slice_empty, List.merge_right, List.merge_right]
    · have active : right.val < stop.val := by
        by_contra! exhausted
        exact endRight (UScalar.eq_of_val_eq (by omega))
      rw [slice_head ids right.val stop.val active fits]
      exact List.cons_merge_cons_pos _ _ _ (by simpa only [keyCompare, decide_eq_true_eq] using keyOrder)

private theorem selection_right (buckets : Nat) (ids : Slice U64) (middle stop left right : Usize)
    (leftRoom : left.val ≤ middle.val) (middleRoom : middle.val ≤ right.val) (rightRoom : right.val < stop.val)
    (fits : stop.val ≤ ids.length) (skip : ¬takeLeft buckets ids middle stop left right) :
    mergeSelection buckets ids middle.val stop.val left.val right.val =
      ids[right.val]! :: mergeSelection buckets ids middle.val stop.val left.val (right.val + 1) := by
  unfold mergeSelection
  rw [slice_head ids right.val stop.val rightRoom fits]
  by_cases active : left.val < middle.val
  · have rejected : ¬keyCompare buckets ids[left.val]! ids[right.val]! := by
      intro yes
      exact skip ⟨active, .inr (of_decide_eq_true yes)⟩
    rw [slice_head ids left.val middle.val active (by omega)]
    exact List.cons_merge_cons_neg _ _ _ rejected
  · have equal : left.val = middle.val := by omega
    rw [equal, slice_empty, List.nil_merge, List.nil_merge]

/-- Every native backward continuation restores exactly the stable merge
suffix, including when passed a later iterator by its caller. -/
def ActualNativeMergeInner : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (ids : Slice U64) (middle stop left right : Usize) (iter : MergeIter) (back : MergeBack),
    0 < shape.capacities.length →
    left.val ≤ middle.val → middle.val ≤ right.val → right.val ≤ stop.val → stop.val ≤ ids.length →
    iter.i ≤ iter.slice.length →
    iter.slice.length - iter.i = (middle.val - left.val) + (stop.val - right.val) →
    ∃ finalBack,
      normalize_loop0_loop0_loop0 field iter back shape ids middle stop left right =
        .ok (⟨iter.slice, iter.slice.length⟩, finalBack) ∧
      ∀ later, finalBack later = back (writeBackList iter.i
        (mergeSelection shape.capacities.length ids middle.val stop.val left.val right.val) later)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem native_merge_inner : ActualNativeMergeInner := by
  intro F field shape ids middle stop left right iter back positive leftRoom middleRoom rightRoom inputRoom
    cursorRoom remaining
  suffices ∀ fuel (left right : Usize) (iter : MergeIter) (back : MergeBack),
      iter.slice.length - iter.i = fuel →
      left.val ≤ middle.val → middle.val ≤ right.val → right.val ≤ stop.val →
      iter.i ≤ iter.slice.length →
      iter.slice.length - iter.i = (middle.val - left.val) + (stop.val - right.val) →
      ∃ finalBack,
        normalize_loop0_loop0_loop0 field iter back shape ids middle stop left right =
          .ok (⟨iter.slice, iter.slice.length⟩, finalBack) ∧
        ∀ later, finalBack later = back (writeBackList iter.i
          (mergeSelection shape.capacities.length ids middle.val stop.val left.val right.val) later) from
    this _ left right iter back rfl leftRoom middleRoom rightRoom cursorRoom remaining
  intro fuel
  induction fuel with
  | zero =>
    intro left right iter back drained leftRoom middleRoom rightRoom cursorRoom remaining
    have endIter : iter.i = iter.slice.length := by omega
    have empty : ¬ iter.i < iter.slice.len.val := by rw [Slice.len_val]; omega
    have next : core.slice.iter.IteratorIterMut.next iter = .ok (none, iter, fun later _ => later) := by
      unfold core.slice.iter.IteratorIterMut.next
      rw [dite_eq_right empty]
    have stopStep : normalize_loop0_loop0_loop0.body field shape ids middle stop iter back left right =
        .ok (.done (iter, back)) := by
      simp only [normalize_loop0_loop0_loop0.body, next, bind_ok]
      rfl
    refine ⟨back, ?_, ?_⟩
    · unfold normalize_loop0_loop0_loop0 loop
      dsimp only
      rw [stopStep, bind_ok]
      have terminal : iter = (⟨iter.slice, iter.slice.length⟩ : MergeIter) := by cases iter; simp_all
      rw [← terminal]
    · intro later
      have leftDone : left.val = middle.val := by omega
      have rightDone : right.val = stop.val := by omega
      simp only [mergeSelection, leftDone, rightDone, slice_empty, List.nil_merge, writeBackList, id]
  | succ fuel ih =>
    intro left right iter back fuelEq leftRoom middleRoom rightRoom cursorRoom remaining
    have active : iter.i < iter.slice.length := by omega
    have max : ids.length ≤ Usize.max := ids.length_ineq
    let advanced : MergeIter := { iter with i := iter.i + 1 }
    have advancedFuel : advanced.slice.length - advanced.i = fuel := by
      change iter.slice.length - (iter.i + 1) = fuel
      omega
    have advancedRoom : advanced.i ≤ advanced.slice.length := by
      change iter.i + 1 ≤ iter.slice.length
      omega
    have step := native_merge_step field shape ids middle stop left right iter back positive
      leftRoom middleRoom rightRoom inputRoom active remaining
    by_cases take : takeLeft shape.capacities.length ids middle stop left right
    · have leftActive := take.1
      let next := usizeWord (left.val + 1)
      let write : MergeBack := fun later => back (writeSelected iter.i ids[left.val]! later)
      have nextVal : next.val = left.val + 1 := word_val _ (by omega)
      have laterRemaining : advanced.slice.length - advanced.i =
          middle.val - next.val + (stop.val - right.val) := by rw [advancedFuel, nextVal]; omega
      obtain ⟨terminalBack, call, restored⟩ := ih next right advanced write advancedFuel
        (by rw [nextVal]; omega) middleRoom rightRoom advancedRoom laterRemaining
      refine ⟨terminalBack, ?_, ?_⟩
      · unfold normalize_loop0_loop0_loop0 loop
        dsimp only
        rw [step, ite_eq_left take, bind_ok]
        exact call
      · intro later
        rw [restored, selection_left _ _ _ _ _ _ middleRoom rightRoom inputRoom take, writeBackList]
        simp only [write, nextVal, advanced]
    · have rightActive : right.val < stop.val := by
        by_contra! exhausted
        have doneRight : right = stop := UScalar.eq_of_val_eq (by omega)
        apply take
        exact ⟨by omega, .inl doneRight⟩
      let next := usizeWord (right.val + 1)
      let write : MergeBack := fun later => back (writeSelected iter.i ids[right.val]! later)
      have nextVal : next.val = right.val + 1 := word_val _ (by omega)
      have laterRemaining : advanced.slice.length - advanced.i =
          middle.val - left.val + (stop.val - next.val) := by rw [advancedFuel, nextVal]; omega
      obtain ⟨terminalBack, call, restored⟩ := ih left next advanced write advancedFuel
        leftRoom (by rw [nextVal]; omega) (by rw [nextVal]; omega) advancedRoom laterRemaining
      refine ⟨terminalBack, ?_, ?_⟩
      · unfold normalize_loop0_loop0_loop0 loop
        dsimp only
        rw [step, ite_eq_right take, bind_ok]
        exact call
      · intro later
        rw [restored, selection_right _ _ _ _ _ _ leftRoom middleRoom rightActive inputRoom take, writeBackList]
        simp only [write, nextVal, advanced]

theorem merge_selection_perm (buckets : Nat) (ids : Slice U64) (middle stop left right : Nat) :
    (mergeSelection buckets ids middle stop left right).Perm (ids.val.slice left middle ++ ids.val.slice right stop) :=
  List.merge_perm_append (keyCompare buckets)

theorem merge_selection_sorted (buckets : Nat) (ids : Slice U64) (middle stop left right : Nat)
    (orderedLeft : (ids.val.slice left middle).Pairwise (fun a b => bucketKey buckets a ≤ bucketKey buckets b))
    (orderedRight : (ids.val.slice right stop).Pairwise (fun a b => bucketKey buckets a ≤ bucketKey buckets b)) :
    (mergeSelection buckets ids middle stop left right).Pairwise (fun a b => bucketKey buckets a ≤ bucketKey buckets b) := by
  have sorted := List.pairwise_merge (le := keyCompare buckets)
    (by intro a b c; simp only [keyCompare, decide_eq_true_eq]; exact Nat.le_trans)
    (by intro a b; simpa only [Bool.or_eq_true, keyCompare, decide_eq_true_eq] using Nat.le_total (bucketKey buckets a) (bucketKey buckets b))
    (ids.val.slice left middle) (ids.val.slice right stop)
    (by simpa only [keyCompare, decide_eq_true_eq] using orderedLeft)
    (by simpa only [keyCompare, decide_eq_true_eq] using orderedRight)
  simpa only [mergeSelection, keyCompare, decide_eq_true_eq] using sorted

#print axioms native_merge_step
#print axioms native_merge_inner

end BulksketchBridge.CandidateNormalization
