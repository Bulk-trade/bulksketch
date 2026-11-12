import Arithmetic.AffineEnumerateGenerated
import BulksketchBridge.ReconstructionLoop

namespace BulksketchBridge.AffineEnumerate

open Aeneas Aeneas.Std ControlFlow
open bulksketch.decode.affine bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

abbrev ScanOutput := Option DecodeFailure × Slice U64 × Nat

/-- Consume the paired point and Horner value lists in order. A successful
exhaustion carries no failure. Early errors retain exactly the previous writes. -/
def scan (degree : Nat) : List (U64 × U64) → Slice U64 → Nat → ScanOutput
  | [], roots, found => (none, roots, found)
  | (point, value) :: rest, roots, found =>
    if value ≠ 0#u64 then scan degree rest roots found
    else if point = 0#u64 then (some .InvalidLocator, roots, found)
    else if found = degree then (some .NotSplit, roots, found)
    else scan degree rest (roots.setAtNat found point) (found + 1)

theorem scan_frame (degree : Nat) (pairs : List (U64 × U64)) (roots : Slice U64) (found : Nat)
    (bounded : found ≤ degree) :
    let result := scan degree pairs roots found
    result.2.1.length = roots.length ∧ found ≤ result.2.2 ∧ result.2.2 ≤ degree := by
  induction pairs generalizing roots found with
  | nil => exact ⟨rfl, le_rfl, bounded⟩
  | cons pair rest ih =>
    obtain ⟨point, value⟩ := pair
    unfold scan
    split
    · exact ih roots found bounded
    split
    · exact ⟨rfl, le_rfl, bounded⟩
    split
    · exact ⟨rfl, le_rfl, bounded⟩
    · have ⟨length, lower, upper⟩ := ih (roots.setAtNat found point) (found + 1) (by omega)
      exact ⟨length.trans (Slice.setAtNat_length ..), by omega, upper⟩

abbrev Zip := core.iter.adapters.zip.Zip (core.slice.iter.Iter U64) (core.slice.iter.Iter U64)

def zipAt (points values : Slice U64) (index : Nat) : Zip :=
  ⟨⟨points, index⟩, ⟨values, index⟩⟩

private abbrev next := Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
  (core.iter.traits.iterator.IteratorSliceIter U64) (core.iter.traits.iterator.IteratorSliceIter U64)

private theorem iter_step (words : Slice U64) (index : Nat) (active : index < words.length) :
    core.slice.iter.IteratorSliceIter.next ⟨words, index⟩ =
      Result.ok (some words[index]!, ⟨words, index + 1⟩) := by
  have fits : index < words.len.val := by rwa [Slice.len_val]
  simp only [core.slice.iter.IteratorSliceIter.next, fits, _root_.dite_true]
  exact congrArg (fun word => Result.ok (some word, (⟨words, index + 1⟩ : core.slice.iter.Iter U64)))
    (Slice.Inhabited_getElem_eq_getElem! words index active)

private theorem iter_done (words : Slice U64) (index : Nat) (finished : words.length ≤ index) :
    core.slice.iter.IteratorSliceIter.next ⟨words, index⟩ =
      Result.ok (none, ⟨words, index⟩) := by
  have beyond : ¬ index < words.len.val := by rw [Slice.len_val]; omega
  simp only [core.slice.iter.IteratorSliceIter.next, beyond, _root_.dite_false]

private theorem drop_cons (words : Slice U64) (index : Nat) (active : index < words.length) :
    words.val.drop index = words[index]! :: words.val.drop (index + 1) := by
  rw [List.drop_eq_getElem_cons (show index < words.val.length from active)]
  exact congrArg (fun word => word :: words.val.drop (index + 1))
    (Slice.Inhabited_getElem_eq_getElem! words index active)

/-- Exact original native candidate scan over aligned slice iterators.
The returned boolean is the generated control bit selecting outer advance.
The error placeholder on exhaustion is unobservable in that branch. -/
def ActualCandidateScan : Prop :=
  ∀ (points values roots : Slice U64) (degree found : Usize) (index : Nat),
    points.length = values.length → degree.val ≤ roots.length → found.val ≤ degree.val →
    ∃ failure written count,
      scan degree.val (List.zip (points.val.drop index) (values.val.drop index)) roots found.val =
        (failure, written, count.val) ∧
      enumerate_loop0_loop1 (zipAt points values index) roots degree found =
        .ok (failure.getD .NotSplit, written, count, failure.isNone) ∧
      written.length = roots.length ∧ count.val ≤ degree.val

theorem candidate_scan_refines : ActualCandidateScan := by
  intro points values roots degree found index aligned capacity starts
  suffices ∀ remaining (index : Nat) (roots : Slice U64) (found : Usize),
      points.length - index = remaining → degree.val ≤ roots.length → found.val ≤ degree.val →
      ∃ failure written count,
        scan degree.val (List.zip (points.val.drop index) (values.val.drop index)) roots found.val =
          (failure, written, count.val) ∧
        enumerate_loop0_loop1 (zipAt points values index) roots degree found =
          .ok (failure.getD .NotSplit, written, count, failure.isNone) ∧
        written.length = roots.length ∧ count.val ≤ degree.val from this _ index roots found rfl capacity starts
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro index roots found remainingEq capacity starts
    by_cases active : index < points.length
    · have activeRight : index < values.length := by omega
      have nextStep : next (zipAt points values index) =
          .ok (some (points[index]!, values[index]!), zipAt points values (index + 1)) := by
        simp only [next, Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
          zipAt]
        simp only [iter_step points index active, iter_step values index activeRight, bind_ok]
        try rfl
      have pairs : List.zip (points.val.drop index) (values.val.drop index) =
          (points[index]!, values[index]!) :: List.zip (points.val.drop (index + 1)) (values.val.drop (index + 1)) := by
        rw [drop_cons points index active, drop_cons values index activeRight]
        rfl
      have unfoldRun {failure : Option DecodeFailure} {written : Slice U64} {count : Usize}
          (body : enumerate_loop0_loop1.body degree (zipAt points values index) roots found =
            .ok (.done (failure.getD .NotSplit, written, count, failure.isNone))) :
          enumerate_loop0_loop1 (zipAt points values index) roots degree found =
            .ok (failure.getD .NotSplit, written, count, failure.isNone) := by
        unfold enumerate_loop0_loop1 loop
        dsimp only
        rw [body]
        simp only [bind_ok]
      have recur {nextRoots : Slice U64} {nextFound : Usize} {failure : Option DecodeFailure}
          {written : Slice U64} {count : Usize}
          (body : enumerate_loop0_loop1.body degree (zipAt points values index) roots found =
            .ok (.cont (zipAt points values (index + 1), nextRoots, nextFound)))
          (normal : enumerate_loop0_loop1 (zipAt points values (index + 1)) nextRoots degree nextFound =
            .ok (failure.getD .NotSplit, written, count, failure.isNone)) :
          enumerate_loop0_loop1 (zipAt points values index) roots degree found =
            .ok (failure.getD .NotSplit, written, count, failure.isNone) := by
        unfold enumerate_loop0_loop1 loop
        dsimp only
        rw [body]
        simpa only [bind_ok, enumerate_loop0_loop1] using normal
      have readNext : Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
        (core.iter.traits.iterator.IteratorSliceIter U64) (core.iter.traits.iterator.IteratorSliceIter U64)
        (zipAt points values index) = .ok (some (points[index]!, values[index]!), zipAt points values (index + 1)) :=
        nextStep
      by_cases nonzero : values[index]! ≠ 0#u64
      · obtain ⟨failure, written, count, folded, normal, length, countBound⟩ :=
          ih (points.length - (index + 1)) (by omega) (index + 1) roots found rfl capacity starts
        refine ⟨failure, written, count, ?_, recur ?_ normal, length, countBound⟩
        · simpa only [pairs, scan, ite_eq_left nonzero] using folded
        · simp only [enumerate_loop0_loop1.body, readNext, bind_ok]
          dsimp! only
          simp only [ite_eq_right nonzero]
      · have zero : values[index]! = 0#u64 := Classical.not_not.mp nonzero
        by_cases zeroPoint : points[index]! = 0#u64
        · refine ⟨some .InvalidLocator, roots, found, ?_, unfoldRun ?_, rfl, starts⟩
          · simp only [pairs, scan, zero, ne_eq, not_true_eq_false, ite_false, zeroPoint, ite_true]
          · simp only [enumerate_loop0_loop1.body, readNext, bind_ok]
            dsimp! only
            simp only [zero, ite_true, zeroPoint]
        · by_cases full : found.val = degree.val
          · have fullWord : found = degree := UScalar.eq_of_val_eq full
            refine ⟨some .NotSplit, roots, found, ?_, unfoldRun ?_, rfl, starts⟩
            · simp only [pairs, scan, zero, ne_eq, not_true_eq_false, ite_false, zeroPoint, full, ite_true]
            · simp only [enumerate_loop0_loop1.body, readNext, bind_ok]
              dsimp! only
              simp only [zero, ite_true, ite_eq_right zeroPoint, fullWord]
          · have canWrite : found.val < roots.length := by omega
            have safe : found.val + (1#usize).val ≤ Usize.max := by
              have fits : roots.length ≤ Usize.max := roots.length_ineq
              change found.val + 1 ≤ Usize.max
              omega
            obtain ⟨advanced, addition, countValue⟩ := RawMulTable.normal_of_spec _ _
              (Usize.add_spec (x := found) (y := 1#usize) safe)
            have nextValue : advanced.val = found.val + 1 := countValue
            have writtenLength : (roots.setAtNat found.val points[index]!).length = roots.length :=
              Slice.setAtNat_length _ _ _
            have wordNe : found ≠ degree := by
              intro equality
              exact full (congrArg UScalar.val equality)
            obtain ⟨failure, written, count, folded, normal, length, countBound⟩ :=
              ih (points.length - (index + 1)) (by omega) (index + 1)
                (roots.setAtNat found.val points[index]!) advanced rfl
                (by rwa [writtenLength]) (by omega)
            refine ⟨failure, written, count, ?_, recur ?_ normal, length.trans writtenLength, countBound⟩
            · simpa only [pairs, scan, zero, ne_eq, not_true_eq_false, ite_false, zeroPoint,
                full, nextValue] using folded
            · simp only [enumerate_loop0_loop1.body, readNext, bind_ok]
              dsimp! only
              simp only [zero, ite_true, ite_eq_right zeroPoint, ite_eq_right wordNe,
                Reconstruction.update_normal _ _ _ canWrite, addition, bind_ok]
    · have emptyLeft : points.val.drop index = [] := by
        apply List.drop_eq_nil_of_le
        change points.length ≤ index
        omega
      have exhausted : next (zipAt points values index) = .ok (none, zipAt points values index) := by
        simp only [next, Aeneas.Std.core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next,
          zipAt]
        simp only [iter_done points index (by omega), bind_ok]
        try rfl
      refine ⟨none, roots, found, by simp [emptyLeft, scan], ?_, rfl, starts⟩
      unfold enumerate_loop0_loop1 loop
      dsimp only
      simp only [enumerate_loop0_loop1.body, exhausted, bind_ok]
      dsimp! only
      simp only [bind_ok]

end BulksketchBridge.AffineEnumerate
