import BulksketchBridge.CandidateMergeInner
import BulksketchBridge.ClosedLeafWindows

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result ControlFlow
open ClosedLeafAdvance (usizeWord word_val)
open bulksketch.sketch.candidates bulksketch.sketch.shape

def mergeMiddle (width count start : Nat) : Nat :=
  start + min width (count - start)

def mergeEnd (width count start : Nat) : Nat :=
  let middle := mergeMiddle width count start
  middle + min width (count - middle)

def mergeBlock (buckets width count start : Nat) (ids temporary : Slice U64) : Slice U64 :=
  let middle := mergeMiddle width count start
  let stop := mergeEnd width count start
  temporary.setSlice! start (mergeSelection buckets ids middle stop start middle)

@[simp] theorem merge_block_length (buckets width count start : Nat) (ids temporary : Slice U64) :
    (mergeBlock buckets width count start ids temporary).length = temporary.length := by
  simp only [mergeBlock, Slice.setSlice!_length]

private theorem write_length (position : Nat) (words : List U64) (later : MergeIter) :
    (writeBackList position words later).slice.length = later.slice.length := by
  induction words generalizing position with
  | nil => rfl
  | cons word rest ih =>
    simp only [writeBackList, writeSelected, Slice.setAtNat_length, ih]

private theorem write_index (position : Nat) (words : List U64) (later : MergeIter) (index : Nat)
    (room : position + words.length ≤ later.slice.length)
    (lower : position ≤ index) (upper : index < position + words.length) :
    (writeBackList position words later).slice[index]! = words[index - position]! := by
  induction words generalizing position with
  | nil => simp only [List.length_nil, Nat.add_zero] at upper; omega
  | cons word rest ih =>
    have enough : position + 1 + rest.length ≤ later.slice.length := by
      simp only [List.length_cons] at room
      omega
    have target : position < (writeBackList (position + 1) rest later).slice.length := by
      rw [write_length]
      omega
    by_cases first : index = position
    · subst index
      simp only [writeBackList, writeSelected, Slice.getElem!_Nat_eq, Nat.sub_self, List.getElem!_cons_zero]
      exact Slice.getElem!_Nat_setAtNat_eq _ _ _ target
    · have tail : index < position + 1 + rest.length := by simp only [List.length_cons] at upper; omega
      have next : position + 1 ≤ index := by omega
      have stable :
          (writeSelected position word (writeBackList (position + 1) rest later)).slice[index]! =
            (writeBackList (position + 1) rest later).slice[index]! := by
        simp only [writeSelected, Slice.getElem!_Nat_eq]
        exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm first)
      rw [writeBackList, stable, ih (position + 1) enough next tail,
        show index - position = index - (position + 1) + 1 by omega, List.getElem!_cons_succ]

private theorem full_write (words : List U64) (later : MergeIter)
    (size : words.length = later.slice.length) :
    (writeBackList 0 words later).slice.val = words := by
  have len : (writeBackList 0 words later).slice.val.length = words.length :=
    (write_length _ _ _).trans size.symm
  apply List.ext_getElem len
  intro index left right
  rw [List.Inhabited_getElem_eq_getElem! _ _ left, List.Inhabited_getElem_eq_getElem! _ _ right,
    ← Slice.getElem!_Nat_eq]
  exact write_index 0 words later index (by omega) (Nat.zero_le _) (by omega)

private theorem merge_len (buckets : Nat) (ids : Slice U64) (start middle stop : Nat)
    (ordered : start ≤ middle) (split : middle ≤ stop) (bounded : stop ≤ ids.length) :
    (mergeSelection buckets ids middle stop start middle).length = stop - start := by
  have idsLen : stop ≤ ids.val.length := bounded
  simp only [mergeSelection, List.length_merge, List.slice_length,
    Nat.min_eq_right (Nat.sub_le_sub_right (split.trans idsLen) start),
    Nat.min_eq_right (Nat.sub_le_sub_right idsLen middle)]
  omega

/-- One complete original merge block, including the range borrow and
the iterator continuation applied through the exact slice write-back. -/
def ActualNativeMergeBlock : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (count width start : Usize) (ids temporary : Slice U64),
    0 < shape.capacities.length → 0 < width.val → start.val < count.val →
    count.val ≤ ids.length → count.val ≤ temporary.length →
    let stop := mergeEnd width.val count.val start.val
    normalize_loop0_loop0.body field shape count ids width temporary start =
      .ok (.cont (mergeBlock shape.capacities.length width.val count.val start.val ids temporary, usizeWord stop)) ∧
    start.val < stop ∧ stop ≤ count.val

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1700000 in
theorem native_merge_block : ActualNativeMergeBlock := by
  intro F field shape count width start ids temporary positive widthPositive active inputRoom outputRoom
  dsimp only
  let middle := mergeMiddle width.val count.val start.val
  let stop := mergeEnd width.val count.val start.val
  have first : start.val < middle := by
    unfold middle mergeMiddle
    have p : 0 < min width.val (count.val - start.val) := Nat.lt_min.mpr ⟨widthPositive, by omega⟩
    omega
  have midBound : middle ≤ count.val := by
    unfold middle mergeMiddle
    have := Nat.min_le_right width.val (count.val - start.val)
    omega
  have middleStop : middle ≤ stop := Nat.le_add_right _ _
  have stopBound : stop ≤ count.val := by
    unfold stop mergeEnd
    change middle + min width.val (count.val - middle) ≤ count.val
    have := Nat.min_le_right width.val (count.val - middle)
    omega
  have max : temporary.length ≤ Usize.max := temporary.length_ineq
  obtain ⟨remaining, subtract, remainingVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := count) (y := start) active.le)
  obtain ⟨mid, middleCall, midVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := start) (y := core.cmp.impls.OrdUsize.min width remaining) (by
      rw [core.cmp.impls.OrdUsize.min_val, remainingVal]
      change middle ≤ _
      omega))
  rw [core.cmp.impls.OrdUsize.min_val, remainingVal] at midVal
  change mid.val = middle at midVal
  obtain ⟨tailLength, tailCall, tailVal, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := count) (y := mid) (by rw [midVal]; exact midBound))
  obtain ⟨finish, endCall, finishVal⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := mid) (y := core.cmp.impls.OrdUsize.min width tailLength) (by
      rw [core.cmp.impls.OrdUsize.min_val, tailVal, midVal]
      change stop ≤ _
      omega))
  rw [core.cmp.impls.OrdUsize.min_val, tailVal, midVal] at finishVal
  change finish.val = stop at finishVal
  have endExact : finish = usizeWord stop :=
    UScalar.eq_of_val_eq (finishVal.trans (word_val _ (by omega)).symm)
  have cut := ClosedLeaf.mutable_region_normal temporary start finish (by rw [finishVal]; omega)
    (by rw [finishVal]; omega)
  let block := ClosedLeaf.region temporary start.val stop
  rw [finishVal] at cut
  have size : block.length = stop - start.val := ClosedLeaf.region_length _ _ _ (by omega)
  let iter : MergeIter := ⟨block, 0⟩
  have iterCall : core.slice.Slice.iter_mut block = .ok (iter, fun (later : MergeIter) => later.slice) := rfl
  obtain ⟨back, mergeCall, restore⟩ := native_merge_inner field shape ids mid finish start mid iter id
    positive (by rw [midVal]; exact first.le) le_rfl (by rw [midVal, finishVal]; exact middleStop)
    (by rw [finishVal]; omega) (Nat.zero_le _) (by
      change block.length - 0 = mid.val - start.val + (finish.val - mid.val)
      rw [size, midVal, finishVal]
      omega)
  let selection := mergeSelection shape.capacities.length ids middle stop start.val middle
  have selectionLength : selection.length = block.length := by
    rw [size]
    exact merge_len _ _ _ _ _ first.le middleStop (by omega)
  have returned : (back (⟨block, block.length⟩ : MergeIter)).slice.val = selection := by
    rw [restore, midVal, finishVal]
    exact full_write selection _ selectionLength
  refine ⟨?_, first.trans_le middleStop, stopBound⟩
  simp only [normalize_loop0_loop0.body, UScalar.lt_equiv, active, ite_true, subtract, lift, bind_ok,
    middleCall, tailCall, endCall, core.slice.index.Slice.index_mut, cut]
  dsimp! only
  have into : bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
      (ClosedLeaf.region temporary start.val stop) = .ok (iter, fun (later : MergeIter) => later.slice) := iterCall
  rw [into, bind_ok]
  dsimp! only
  have merged : normalize_loop0_loop0_loop0 field iter (fun im : MergeIter => im) shape ids mid finish start mid =
      .ok (⟨iter.slice, iter.slice.length⟩, back) := mergeCall
  rw [merged, bind_ok]
  dsimp! only
  rw [returned, endExact]
  rfl

def mergePassFrom (buckets width count : Nat) (ids : Slice U64) :
    Nat → Nat → Slice U64 → Slice U64
  | 0, _, temporary => temporary
  | fuel + 1, start, temporary =>
    if start < count then mergePassFrom buckets width count ids fuel (mergeEnd width count start)
      (mergeBlock buckets width count start ids temporary)
    else temporary

@[simp] theorem merge_pass_length (buckets width count : Nat) (ids : Slice U64)
    (fuel start : Nat) (temporary : Slice U64) :
    (mergePassFrom buckets width count ids fuel start temporary).length = temporary.length := by
  induction fuel generalizing start temporary with
  | zero => rfl
  | succ fuel ih =>
    unfold mergePassFrom
    split
    · rw [ih, merge_block_length]
    · rfl

/-- The original middle loop performs exactly the model's successive
capped merge blocks. Its read array is constant through the pass. -/
def ActualNativeMergePass : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (count width start : Usize) (ids temporary : Slice U64) (fuel : Nat),
    0 < shape.capacities.length → 0 < width.val →
    start.val ≤ count.val → count.val ≤ ids.length → count.val ≤ temporary.length →
    count.val - start.val ≤ fuel →
    normalize_loop0_loop0 field shape count ids temporary width start =
      .ok (mergePassFrom shape.capacities.length width.val count.val ids fuel start.val temporary)

private theorem merge_pass_end {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (count width start : Usize) (ids temporary : Slice U64) (done : ¬start.val < count.val) :
    normalize_loop0_loop0 field shape count ids temporary width start = .ok temporary := by
  have step : normalize_loop0_loop0.body field shape count ids width temporary start =
      .ok (.done temporary) := by
    simp only [normalize_loop0_loop0.body, UScalar.lt_equiv, done, ite_false]
  unfold normalize_loop0_loop0 loop
  dsimp only
  rw [step, bind_ok]

theorem native_merge_pass : ActualNativeMergePass := by
  intro F field shape count width start ids temporary fuel positive widthPositive ordered inputRoom outputRoom remaining
  induction fuel generalizing start temporary with
  | zero =>
    exact merge_pass_end field shape count width start ids temporary (by omega)
  | succ fuel ih =>
    by_cases active : start.val < count.val
    · obtain ⟨step, advanced, stopBound⟩ :=
        native_merge_block field shape count width start ids temporary positive widthPositive active inputRoom outputRoom
      let stop := mergeEnd width.val count.val start.val
      let updated := mergeBlock shape.capacities.length width.val count.val start.val ids temporary
      have size : temporary.length ≤ Usize.max := temporary.length_ineq
      have stopVal : (usizeWord stop).val = stop := word_val _ (by omega)
      have next := ih (usizeWord stop) updated (by rw [stopVal]; exact stopBound)
        (by rw [merge_block_length]; exact outputRoom) (by rw [stopVal]; omega)
      unfold normalize_loop0_loop0 loop
      dsimp only
      rw [step, bind_ok]
      simpa only [normalize_loop0_loop0, stopVal, mergePassFrom, active, ite_true] using next
    · simpa only [mergePassFrom, active, ite_false] using
        merge_pass_end field shape count width start ids temporary active

#print axioms native_merge_block
#print axioms native_merge_pass

end BulksketchBridge.CandidateNormalization
