import Arithmetic.CandidateInnerGenerated
import BulksketchBridge.ReconstructionLoop

namespace BulksketchBridge.CandidateInner

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.stages.Execution

abbrev Reply := Nat × Slice U64 × Bool

/-- Scan candidate pairs in order, writing every zero evaluation until the
next zero would exceed the locator degree. Prior successful writes remain
in the result of either exit. -/
def scan (degree : Nat) : List (U64 × U64) → Slice U64 → Nat → Reply
  | [], roots, hits => (hits, roots, false)
  | (point, value) :: rest, roots, hits =>
    if value = 0#u64 then
      if hits = degree then (hits, roots, true)
      else scan degree rest (roots.setAtNat hits point) (hits + 1)
    else scan degree rest roots hits

abbrev Zip := core.iter.adapters.zip.Zip (core.slice.iter.Iter U64) (core.slice.iter.Iter U64)

def zipAt (points values : Slice U64) (index : Nat) : Zip :=
  ⟨⟨points, index⟩, ⟨values, index⟩⟩

private abbrev zipNext := Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
  (core.iter.traits.iterator.IteratorSliceIter U64) (core.iter.traits.iterator.IteratorSliceIter U64)

private theorem iter_step (words : Slice U64) (index : Nat) (active : index < words.length) :
    core.slice.iter.IteratorSliceIter.next ⟨words, index⟩ =
      .ok (some words[index]!, ⟨words, index + 1⟩) := by
  have fits : index < words.len.val := by rwa [Slice.len_val]
  simp only [core.slice.iter.IteratorSliceIter.next, fits, _root_.dite_true]
  exact congrArg (fun word => Result.ok (some word, (⟨words, index + 1⟩ : core.slice.iter.Iter U64)))
    (Slice.Inhabited_getElem_eq_getElem! words index active)

private theorem iter_done (words : Slice U64) (index : Nat) (finished : words.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next ⟨words, index⟩ = .ok (none, ⟨words, index⟩) := by
  have beyond : ¬ index < words.len.val := by rw [Slice.len_val]; omega
  simp only [core.slice.iter.IteratorSliceIter.next, beyond, _root_.dite_false]

private theorem drop_cons (words : Slice U64) (index : Nat) (active : index < words.length) :
    words.val.drop index = words[index]! :: words.val.drop (index + 1) := by
  rw [List.drop_eq_getElem_cons (show index < words.val.length from active)]
  exact congrArg (fun word => word :: words.val.drop (index + 1))
    (Slice.Inhabited_getElem_eq_getElem! words index active)

/-- Exact source scan for a chunk paired with the entire values buffer.
The buffer can be wider than the chunk, as on the last source iteration. -/
def ActualNativeCandidateInner : Prop :=
  ∀ (points values roots : Slice U64) (degree hits : Usize) (index : Nat),
    points.length ≤ values.length →
    degree.val ≤ roots.length →
    hits.val ≤ degree.val →
    ∃ count written reject,
      scan degree.val (List.zip (points.val.drop index) (values.val.drop index)) roots hits.val =
        (count.val, written, reject) ∧
      candidates_loop0_loop0 (zipAt points values index) degree hits roots false =
        .ok (count, written, reject)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1300000 in
theorem native_candidate_inner : ActualNativeCandidateInner := by
  intro points values roots degree hits index wide capacity valid
  suffices ∀ remaining (index : Nat) (roots : Slice U64) (hits : Usize),
      points.length - index = remaining → degree.val ≤ roots.length → hits.val ≤ degree.val →
      ∃ count written reject,
        scan degree.val (List.zip (points.val.drop index) (values.val.drop index)) roots hits.val =
          (count.val, written, reject) ∧
        candidates_loop0_loop0 (zipAt points values index) degree hits roots false =
          .ok (count, written, reject) from this _ index roots hits rfl capacity valid
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro index roots hits remainingEq capacity valid
    have step {count : Usize} {written : Slice U64} {reject : Bool}
        (body : candidates_loop0_loop0.body degree false (zipAt points values index) hits roots =
          .ok (.done (count, written, reject))) :
        candidates_loop0_loop0 (zipAt points values index) degree hits roots false =
          .ok (count, written, reject) := by
      unfold candidates_loop0_loop0 loop
      dsimp only
      rw [body, bind_ok]
    by_cases active : index < points.length
    · have activeRight : index < values.length := by omega
      have next : zipNext (zipAt points values index) =
          .ok (some (points[index]!, values[index]!), zipAt points values (index + 1)) := by
        simp only [zipNext, Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
          zipAt, iter_step points index active, iter_step values index activeRight, bind_ok]
        rfl
      have pairs : List.zip (points.val.drop index) (values.val.drop index) =
          (points[index]!, values[index]!) :: List.zip (points.val.drop (index + 1)) (values.val.drop (index + 1)) := by
        rw [drop_cons points index active, drop_cons values index activeRight]
        rfl
      have recur {nextRoots : Slice U64} {nextHits count : Usize} {written : Slice U64} {reject : Bool}
          (body : candidates_loop0_loop0.body degree false (zipAt points values index) hits roots =
            .ok (.cont (zipAt points values (index + 1), nextHits, nextRoots)))
          (normal : candidates_loop0_loop0 (zipAt points values (index + 1)) degree nextHits nextRoots false =
            .ok (count, written, reject)) :
          candidates_loop0_loop0 (zipAt points values index) degree hits roots false =
            .ok (count, written, reject) := by
        unfold candidates_loop0_loop0 loop
        dsimp only
        rw [body]
        simpa only [bind_ok, candidates_loop0_loop0] using normal
      by_cases zero : values[index]! = 0#u64
      · by_cases full : hits.val = degree.val
        · have same : hits = degree := UScalar.eq_of_val_eq full
          refine ⟨hits, roots, true, ?_, step ?_⟩
          · simp only [pairs, scan, zero, ite_true, full]
          · simp only [candidates_loop0_loop0.body, next, bind_ok]
            dsimp! only
            simp only [zero, ite_true, same]
        · have room : hits.val < roots.length := by omega
          have fits : hits.val + (1#usize).val ≤ Usize.max := by
            have max : roots.length ≤ Usize.max := roots.length_ineq
            change hits.val + 1 ≤ Usize.max
            omega
          obtain ⟨advanced, added, nextValue⟩ := RawMulTable.normal_of_spec _ _
            (Usize.add_spec (x := hits) (y := 1#usize) fits)
          change advanced.val = hits.val + 1 at nextValue
          have length := Slice.setAtNat_length roots hits.val points[index]!
          have different : hits ≠ degree := fun same => full (congrArg UScalar.val same)
          obtain ⟨count, written, reject, modeled, native⟩ :=
            ih (points.length - (index + 1)) (by omega) (index + 1)
              (roots.setAtNat hits.val points[index]!) advanced rfl (by rwa [length]) (by omega)
          refine ⟨count, written, reject, ?_, recur ?_ native⟩
          · simpa only [pairs, scan, zero, ite_true, full, ite_false, nextValue] using modeled
          · simp only [candidates_loop0_loop0.body, next, bind_ok]
            dsimp! only
            simp only [zero, ite_true, ite_eq_right different,
              Reconstruction.update_normal _ _ _ room, added, bind_ok]
      · obtain ⟨count, written, reject, modeled, native⟩ :=
          ih (points.length - (index + 1)) (by omega) (index + 1) roots hits rfl capacity valid
        refine ⟨count, written, reject, ?_, recur ?_ native⟩
        · simpa only [pairs, scan, ite_eq_right zero] using modeled
        · simp only [candidates_loop0_loop0.body, next, bind_ok]
          dsimp! only
          simp only [ite_eq_right zero]
    · have endLeft : points.val.drop index = [] := by
        apply List.drop_eq_nil_of_le
        change points.length ≤ index
        omega
      have exhausted : zipNext (zipAt points values index) =
          .ok (none, zipAt points values index) := by
        simp only [zipNext, Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
          zipAt, iter_done points index (by omega), bind_ok]
        rfl
      refine ⟨hits, roots, false, by simp only [endLeft, List.zip_nil_left, scan], step ?_⟩
      simp only [candidates_loop0_loop0.body, exhausted, bind_ok]
      rfl

/-- Exactly the candidate points whose paired locator values are zero. -/
def zeroPoints : List (U64 × U64) → List U64
  | [] => []
  | (point, value) :: rest =>
    if value = 0#u64 then point :: zeroPoints rest else zeroPoints rest

private theorem take_updated {α : Type} (words : List α) (index : Nat) (point : α)
    (inside : index < words.length) :
    (words.set index point).take (index + 1) = words.take index ++ [point] := by
  induction words generalizing index with
  | nil => simp at inside
  | cons word rest ih =>
    cases index with
    | zero => rfl
    | succ index =>
      have active : index < rest.length := by simp only [List.length_cons] at inside; omega
      change word :: (rest.set index point).take (index + 1) = word :: (rest.take index ++ [point])
      rw [ih index active]

private theorem drop_updated {α : Type} (words : List α) (index finish : Nat) (point : α)
    (outside : index < finish) : (words.set index point).drop finish = words.drop finish := by
  induction words generalizing index finish with
  | nil => simp
  | cons word rest ih =>
    cases finish with
    | zero => omega
    | succ finish =>
      cases index with
      | zero => rfl
      | succ index =>
        change (rest.set index point).drop finish = rest.drop finish
        exact ih index finish (by omega)

/-- Full frame for the scan result. The contiguous output is exactly the
accepted prefix of zero evaluations. Rejection is the first excess zero,
and every word outside the written interval keeps its original value. -/
def ScanFrame (degree : Nat) (pairs : List (U64 × U64)) (roots : Slice U64)
    (hits : Nat) (result : Reply) : Prop :=
  let zeros := zeroPoints pairs
  let accepted := zeros.take (degree - hits)
  result.1 = hits + accepted.length ∧ result.1 ≤ degree ∧
  result.2.1.length = roots.length ∧
  result.2.1.val = roots.val.take hits ++ accepted ++ roots.val.drop (hits + accepted.length) ∧
  result.2.2 = decide (degree - hits < zeros.length)

theorem scan_frame (degree : Nat) (pairs : List (U64 × U64)) (roots : Slice U64)
    (hits : Nat) (capacity : degree ≤ roots.length) (bounded : hits ≤ degree) :
    ScanFrame degree pairs roots hits (scan degree pairs roots hits) := by
  induction pairs generalizing roots hits with
  | nil =>
    simp only [ScanFrame, zeroPoints, scan, List.take_nil, List.length_nil, Nat.add_zero,
      List.append_nil, List.take_append_drop, Nat.not_lt_zero, decide_false, true_and]
    exact ⟨bounded, trivial⟩
  | cons pair rest ih =>
    obtain ⟨point, value⟩ := pair
    by_cases zero : value = 0#u64
    · by_cases full : hits = degree
      · subst hits
        simp only [ScanFrame, zeroPoints, scan, zero, ite_true, Nat.sub_self, List.take_zero,
          List.length_nil, Nat.add_zero, le_refl, List.append_nil, List.take_append_drop,
          List.length_cons, Nat.zero_lt_succ, decide_true, and_self]
      · have active : hits < roots.length := by omega
        have length := Slice.setAtNat_length roots hits point
        let updated := roots.setAtNat hits point
        have nextCapacity : degree ≤ updated.length := by simpa only [updated, length] using capacity
        have nextBound : hits + 1 ≤ degree := by omega
        have room : degree - hits = (degree - (hits + 1)) + 1 := by omega
        let accepted := (zeroPoints rest).take (degree - (hits + 1))
        let result := scan degree rest updated (hits + 1)
        have frame := ih updated (hits + 1) nextCapacity nextBound
        obtain ⟨count, bound, sameLength, output, reject⟩ := frame
        change result.1 = hits + 1 + accepted.length at count
        change result.2.1.val = updated.val.take (hits + 1) ++ accepted ++
          updated.val.drop (hits + 1 + accepted.length) at output
        have updatedVal : updated.val = roots.val.set hits point := by
          simp [updated, Slice.setAtNat]
        have headFrame : updated.val.take (hits + 1) = roots.val.take hits ++ [point] := by
          rw [updatedVal]
          exact take_updated roots.val hits point active
        have suffix : updated.val.drop (hits + 1 + accepted.length) =
            roots.val.drop (hits + 1 + accepted.length) := by
          rw [updatedVal]
          exact drop_updated roots.val hits (hits + 1 + accepted.length) point (by omega)
        simp only [ScanFrame, zeroPoints, scan, zero, full, ite_true, ite_false, room, List.take_succ_cons]
        change result.1 = hits + (point :: accepted).length ∧ result.1 ≤ degree ∧
          result.2.1.length = roots.length ∧ result.2.1.val =
            roots.val.take hits ++ (point :: accepted) ++ roots.val.drop (hits + (point :: accepted).length) ∧ _
        refine ⟨by rw [count, List.length_cons]; omega, bound, sameLength.trans length, ?_, reject.trans ?_⟩
        · rw [output, headFrame, suffix, List.length_cons, show hits + 1 + accepted.length =
            hits + (accepted.length + 1) by omega]
          simp only [List.append_assoc, List.singleton_append]
        · rw [List.length_cons]
          simp only [Nat.add_lt_add_iff_right]
    · simpa only [ScanFrame, zeroPoints, scan, ite_eq_right zero] using ih roots hits capacity bounded

/-- The actual generated scan returns the exact hit count, overflow decision,
and accepted candidate prefix, including the mutable root-slice frame. -/
def ActualNativeCandidateInnerFrame : Prop :=
  ∀ (points values roots : Slice U64) (degree hits : Usize) (index : Nat),
    points.length ≤ values.length →
    degree.val ≤ roots.length →
    hits.val ≤ degree.val →
    ∃ count written reject,
      candidates_loop0_loop0 (zipAt points values index) degree hits roots false =
        .ok (count, written, reject) ∧
      ScanFrame degree.val (List.zip (points.val.drop index) (values.val.drop index)) roots hits.val
        (count.val, written, reject)

theorem native_candidate_inner_frame : ActualNativeCandidateInnerFrame := by
  intro points values roots degree hits index width capacity bounded
  obtain ⟨count, written, reject, model, native⟩ :=
    native_candidate_inner points values roots degree hits index width capacity bounded
  refine ⟨count, written, reject, native, ?_⟩
  rw [← model]
  exact scan_frame _ _ _ _ capacity bounded

#print axioms native_candidate_inner
#print axioms native_candidate_inner_frame

end BulksketchBridge.CandidateInner
