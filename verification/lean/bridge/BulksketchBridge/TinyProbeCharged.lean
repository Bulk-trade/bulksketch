import BulksketchBridge.TinyProbe
import BulksketchBridge.CanonicalizeWrapper
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.TinyProbe

open Aeneas Aeneas.Std Result DenseCoefficient RebuiltLfsr
open Aeneas.Std.ReconstructionRuntime
open BulksketchBridge.CanonicalizeOrdering
open Aeneas.Std.CanonicalizeRuntime
open bulksketch.backend.contract bulksketch.decode.probe bulksketch.decode.row bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

abbrev ChargedFrame := RowProgress × Probe × Slice U64 × Slice U64

def progress (stage : Stage) : RowProgress :=
  ⟨stage, 0#usize, 0#usize, 0#usize, 0#usize⟩

private theorem read (words : Slice U64) (index : Usize) (inside : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨actual, normal, exactWord⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index inside)
  rw [normal, exactWord, Slice.getElem!_Nat_eq]
  exact congrArg Result.ok (List.Inhabited_getElem_eq_getElem! _ _ inside)

private theorem write (words : Slice U64) (index : Usize) (value : U64) (inside : index.val < words.length) :
    Slice.update words index value = .ok (words.setAtNat index.val value) := by
  obtain ⟨actual, normal, exactWords⟩ := RawMulTable.normal_of_spec _ _ (Slice.update_spec words index value inside)
  rw [normal, exactWords]
  rfl

private theorem direct_one {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Probe) (difference verification roots : Slice U64)
    (stage : self.next = some .DirectOne) (input : 0 < difference.length) (output : 0 < roots.length) :
    Probe.run_charged field kernels self difference verification roots =
      .ok (progress .DirectOne, {self with next := some .Verification, count := 1#usize},
        verification, roots.setAtNat 0 difference[0]!) := by
  simp only [Probe.run_charged, stage, core.option.Option.expect, ofOption, bind_ok,
    read difference 0#usize input, write roots 0#usize _ output]
  rfl

def directTwoExpected {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Probe) (difference verification roots : Slice U64) : Result ChargedFrame := do
  let pair ← bulksketch.decode.direct.two field kernels difference[0]! difference[1]!
  match pair with
  | none =>
    let after ← Probe.reject self difference.len
    .ok (progress .DirectTwo, after, verification, roots)
  | some hit =>
    .ok (progress .DirectTwo, {self with next := some .Verification, count := 2#usize},
      verification, restorePrefix roots hit.roots.to_slice)

private theorem direct_two {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Probe) (difference verification roots : Slice U64)
    (stage : self.next = some .DirectTwo) (input : 2 ≤ difference.length) (output : 2 ≤ roots.length) :
    Probe.run_charged field kernels self difference verification roots =
      directTwoExpected field kernels self difference verification roots := by
  have readZero := read difference 0#usize (by change 0 < difference.length; omega)
  have readOne := read difference 1#usize (by change 1 < difference.length; omega)
  simp only [Probe.run_charged, stage, core.option.Option.expect, ofOption, bind_ok,
    readZero, readOne, directTwoExpected]
  refine congrArg (fun arm => Aeneas.Std.bind
    (bulksketch.decode.direct.two field kernels difference[0]! difference[1]!) arm) ?_
  funext pair
  cases pair with
  | none => rfl
  | some hit =>
    have length : (prefixSlice roots 2).length = hit.roots.to_slice.length := by
      simp [prefix_length, Nat.min_eq_left output]
    dsimp only
    rw [Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefix_normal roots 2#usize output, bind_ok]
    dsimp! only
    simp only [lift, bind_ok, show (2#usize).val = 2 from rfl]
    rw [ClosedLeaf.copy_normal _ _ length, bind_ok]
    rfl

def canonicalExpected (self : Probe) (verification roots : Slice U64) : Result ChargedFrame := do
  let ordered ← if self.count = 2#usize ∧ roots[0]! > roots[1]! then
    core.slice.Slice.swap roots 0#usize 1#usize else .ok roots
  .ok (progress .Canonicalization, {self with next := none}, verification, ordered)

private theorem canonical {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (self : Probe) (difference verification roots : Slice U64)
    (stage : self.next = some .Canonicalization) (output : self.count = 2#usize → 2 ≤ roots.length) :
    Probe.run_charged field kernels self difference verification roots =
      canonicalExpected self verification roots := by
  simp only [Probe.run_charged, stage, core.option.Option.expect, ofOption, bind_ok, canonicalExpected]
  by_cases count : self.count = 2#usize
  · have readZero := read roots 0#usize (by have := output count; change 0 < roots.length; omega)
    have readOne := read roots 1#usize (by have := output count; change 1 < roots.length; omega)
    simp only [count, ite_true, true_and, readZero, readOne, bind_ok]
    have readZeroIndex : (0#usize).val = 0 := rfl
    have readOneIndex : (1#usize).val = 1 := rfl
    simp only [readZeroIndex, readOneIndex]
    by_cases order : roots[0]! > roots[1]! <;>
      simp only [order, ite_true, ite_false, bind_ok, progress]
  · simp only [count, ite_false, false_and, bind_ok]
    rfl

def valid (mask word : U64) : Bool := decide (word ≠ 0#u64 ∧ word &&& ~~~mask = 0#u64)

private theorem all_scan {C : Type} (call : C → U64 → Result (Bool × C))
    (predicate : U64 → Bool) (correct : ∀ state word, call state word = .ok (predicate word, state))
    (words : List U64) (state : C) :
    ∃ count, ReconstructionRuntime.scan call words state = .ok (words.all predicate, count) := by
  induction words with
  | nil => exact ⟨0, rfl⟩
  | cons word rest ih =>
    cases passes : predicate word with
    | false => exact ⟨1, by simp [ReconstructionRuntime.scan, correct, passes]⟩
    | true =>
      obtain ⟨count, tail⟩ := ih
      exact ⟨count+1, by simp [ReconstructionRuntime.scan, correct, passes, tail]⟩

private theorem valid_scan {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask : U64) (exactMask : field.MASK = .ok mask) (words : Slice U64) :
    ∃ endIt, sliceAll
      (Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool field kernels)
      ⟨words, 0⟩ () = .ok (words.val.all (valid mask), endIt) := by
  let callback := Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool field kernels
  have step : ∀ (state : Unit) word, callback.call_mut state word = .ok (valid mask word, state) := by
    intro state word
    cases state
    by_cases zero : word = 0#u64
    · simp [callback, Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut,
        zero, valid]
    · simp [callback, Probe.run_charged.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut,
        exactMask, zero, valid, lift]
  obtain ⟨consumed, normal⟩ := all_scan callback.call_mut (valid mask) step words.val ()
  refine ⟨⟨words, consumed⟩, ?_⟩
  change sliceAll callback ⟨words, 0⟩ () = _
  simp only [sliceAll, List.drop_zero, normal, bind_ok, Nat.zero_add]
  rfl

private theorem duplicate_scan {F K : Type} (field : bulksketch.field.BinaryField F)
    (kernels : BulkKernels K F) (words : Slice U64) :
    ∃ endIt, anyWindows ()
      (Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool field kernels)
      ((pairWindows words.val).map fun pair => pairSlice pair.1 pair.2) () =
      .ok (adjacentDuplicate words.val, endIt) := by
  let callback := Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool field kernels
  have step : ∀ (state : Unit) (pair : U64 × U64), callback.call_mut state (pairSlice pair.1 pair.2) =
      .ok (decide (pair.1 = pair.2), state) := by
    intro state pair
    cases state
    simp [callback, Probe.run_charged.closure_1.Insts.CoreOpsFunctionFnMutTupleShared0SliceU64Bool.call_mut,
      pairSlice, Slice.index_usize, Slice.from_val]
  obtain ⟨count, normal⟩ := CanonicalizeWrapper.scan_refines callback
    (fun pair : U64 × U64 => pairSlice pair.1 pair.2) (fun pair => decide (pair.1 = pair.2))
    step (pairWindows words.val) ()
  rw [windows_any_duplicate] at normal
  refine ⟨((pairWindows words.val).map fun pair => pairSlice pair.1 pair.2).drop count, ?_⟩
  change anyWindows () callback _ () = _
  simp only [anyWindows, normal, bind_ok]
  rfl

def verificationExpected {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask : U64) (self : Probe) (difference verification roots : Slice U64) : Result ChargedFrame := do
  let seen := prefixSlice roots self.count.val
  if seen.len ≤ self.budget.nonzero ∧ seen.val.all (valid mask) ∧ !adjacentDuplicate seen.val then
    let (accepted, written) ← verified field kernels difference seen verification
    if accepted then
      .ok (progress .Verification, {self with next := some .Canonicalization}, written, roots)
    else
      let after ← Probe.reject self difference.len
      .ok (progress .Verification, after, written, roots)
  else
    let after ← Probe.reject self difference.len
    .ok (progress .Verification, after, verification, roots)

private theorem verification_stage {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask : U64) (exactMask : field.MASK = .ok mask)
    (self : Probe) (difference verification roots : Slice U64)
    (stage : self.next = some .Verification) (output : self.count.val ≤ roots.length) :
    Probe.run_charged field kernels self difference verification roots =
      verificationExpected field kernels mask self difference verification roots := by
  let seen := prefixSlice roots self.count.val
  obtain ⟨endIt, all⟩ := valid_scan field kernels mask exactMask seen
  obtain ⟨endWindows, adjacent⟩ := duplicate_scan field kernels seen
  simp only [Probe.run_charged, stage, core.option.Option.expect, ofOption, bind_ok,
    Slice.index_SliceIndexRangeToUsizeSliceInst, shared_prefix_normal roots self.count output, verificationExpected]
  change _ = _
  by_cases capacity : seen.len ≤ self.budget.nonzero
  · simp only [seen] at capacity all adjacent
    simp only [capacity, ite_true, true_and, core.slice.Slice.iter, bind_ok, all]
    dsimp! only
    by_cases canonical : (prefixSlice roots self.count.val).val.all (valid mask) = true
    · simp only [canonical, ite_true, true_and, windows, bind_ok, adjacent]
      dsimp! only
      cases adjacentDuplicate (prefixSlice roots self.count.val).val <;> rfl
    · have failed : (prefixSlice roots self.count.val).val.all (valid mask) = false :=
        Bool.eq_false_iff.mpr canonical
      simp only [failed, Bool.false_eq_true, ite_false, false_and]
      rfl
  · simp only [seen] at capacity
    simp only [capacity, ite_false, false_and]
    rfl

/-- All four admitted charged transitions of the original tiny probe. The
DirectTwo and Verification branches call their exact native subroutines. -/
def ActualTinyProbeRunCharged : Prop :=
  ∀ {F K : Type} (field : bulksketch.field.BinaryField F) (kernels : BulkKernels K F)
    (mask : U64), field.MASK = .ok mask →
    ∀ (self : Probe) (difference verification roots : Slice U64),
      (self.next = some .DirectOne → 0 < difference.length ∧ 0 < roots.length) →
      (self.next = some .DirectTwo → 2 ≤ difference.length ∧ 2 ≤ roots.length) →
      (self.next = some .Verification → self.count.val ≤ roots.length) →
      (self.count = 2#usize → 2 ≤ roots.length) →
      Probe.run_charged field kernels self difference verification roots =
        match self.next with
        | some .DirectOne =>
          .ok (progress .DirectOne, {self with next := some .Verification, count := 1#usize},
            verification, roots.setAtNat 0 difference[0]!)
        | some .DirectTwo => directTwoExpected field kernels self difference verification roots
        | some .Verification => verificationExpected field kernels mask self difference verification roots
        | some .Canonicalization => canonicalExpected self verification roots
        | _ => .fail .panic

theorem tiny_probe_run_charged : ActualTinyProbeRunCharged := by
  intro F K field kernels mask exactMask self difference verification roots one two verify canonicalBound
  cases stage : self.next with
  | none => simp [Probe.run_charged, stage, core.option.Option.expect]
  | some status =>
    cases status
    all_goals first
      | exact direct_one field kernels self difference verification roots stage (one stage).1 (one stage).2
      | exact direct_two field kernels self difference verification roots stage (two stage).1 (two stage).2
      | exact verification_stage field kernels mask exactMask self difference verification roots stage (verify stage)
      | exact canonical field kernels self difference verification roots stage canonicalBound
      | simp [Probe.run_charged, stage, core.option.Option.expect]

#print axioms tiny_probe_run_charged

end BulksketchBridge.TinyProbe
