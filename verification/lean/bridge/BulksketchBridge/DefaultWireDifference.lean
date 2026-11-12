import Arithmetic.DefaultWireDifferenceGenerated
import BulksketchBridge.MutableZip
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.DefaultWireDifference

open Aeneas Aeneas.Std Result ControlFlow DefaultWireDifferenceRuntime
open bulksketch.backend.contract.BulkKernels

set_option maxRecDepth 2048
set_option maxHeartbeats 450000

def leWord (bytes : List U8) : U64 :=
  if h : bytes.length = (8#usize).val then
    core.num.U64.from_le_bytes (Array.from bytes h)
  else 0#u64

def wordsFrom (localWords : Slice U64) (position : Nat) : List (List U8) → List U64
  | [] => []
  | bytes :: rest => (localWords[position]! ^^^ leWord bytes) ::
      wordsFrom localWords (position + 1) rest

def writeFrom (destination : Slice U64) (position : Nat) : List U64 → Slice U64
  | [] => destination
  | word :: rest => (writeFrom destination (position + 1) rest).setAtNat position word

@[simp] theorem wordsFrom_length (localWords : Slice U64) (position : Nat)
    (chunks : List (List U8)) :
    (wordsFrom localWords position chunks).length = chunks.length := by
  induction chunks generalizing position with
  | nil => rfl
  | cons _ rest ih => simp [wordsFrom, ih]

@[simp] theorem writeFrom_length (destination : Slice U64) (position : Nat) (words : List U64) :
    (writeFrom destination position words).length = destination.length := by
  induction words generalizing position with
  | nil => rfl
  | cons _ rest ih => simp [writeFrom, Slice.setAtNat_length, ih]

theorem writeFrom_word (destination : Slice U64) (position : Nat) (words : List U64)
    (room : position + words.length ≤ destination.length) (index : Nat) (bounded : index < words.length) :
    (writeFrom destination position words)[position + index]! = words[index] := by
  induction words generalizing position index with
  | nil => simp at bounded
  | cons word rest ih =>
    cases index with
    | zero =>
      simp only [writeFrom, Nat.add_zero, Slice.getElem!_Nat_eq]
      rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by
        have active : position < destination.length := by simp only [List.length_cons] at room; omega
        simpa only [Slice.length, writeFrom_length] using active)]
      rfl
    | succ index =>
      simp only [writeFrom, Slice.getElem!_Nat_eq]
      rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega), ← Slice.getElem!_Nat_eq]
      rw [show position + (index + 1) = position + 1 + index by omega]
      exact ih _ (by simp only [List.length_cons] at room; omega) _ (by simpa using bounded)

def stateAt (destination localWords : Slice U64) (position : Nat)
    (chunks : List (Slice U8)) (remainder : Slice U8) : State :=
  ⟨MutableZip.stateAt destination localWords position, ⟨chunks, remainder⟩⟩

def replace (state : State) (position : Nat) (word : U64) : State :=
  ⟨MutableZip.replaceLeft state.fst position word, state.snd⟩

private theorem next_live (destination localWords : Slice U64) (position : Nat)
    (head : Slice U8) (rest : List (Slice U8)) (remainder : Slice U8)
    (leftBound : position < destination.length) (rightBound : position < localWords.length) :
    next
      (innerDictionary (bulksketch.core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT U64)
        (core.iter.traits.iterator.IteratorSliceIter U64))
      (core.iter.traits.iterator.IteratorChunksExact U8)
      (stateAt destination localWords position (head :: rest) remainder) =
      .ok (some ((destination[position], localWords[position]), head),
        stateAt destination localWords (position + 1) rest remainder,
        fun later replacement => match replacement with
          | none => later
          | some item => replace later position item.1.1) := by
  have inner := MutableZip.next_some_at destination localWords position leftBound rightBound
  simp only [next, stateAt, innerDictionary]
  rw [show MutableZip.next _ _ _ = _ from inner, bind_ok]
  dsimp! only
  simp only [bind_ok]
  dsimp! only
  congr 3
  funext later replacement
  cases later
  cases replacement <;> rfl

private theorem try_from_exact (bytes : Slice U8) (full : bytes.length = 8) :
    core.array.TryFromArrayCopySlice.try_from 8#usize core.marker.CopyU8 bytes =
      .ok (.Ok (Array.from bytes.val (show bytes.val.length = (8#usize).val from full))) := by
  unfold core.array.TryFromArrayCopySlice.try_from
  rw [dite_eq_left (show bytes.length = (8#usize).val from full)]

private theorem step_live (destination localWords : Slice U64) (position : Nat)
    (head : Slice U8) (rest : List (Slice U8)) (remainder : Slice U8)
    (leftBound : position < destination.length) (rightBound : position < localWords.length)
    (full : head.length = 8) (back : Back) (any : U64) :
    difference.default_loop.body
      (stateAt destination localWords position (head :: rest) remainder) back any =
      .ok (.cont (stateAt destination localWords (position + 1) rest remainder,
        fun later => back (replace later position (localWords[position]! ^^^ leWord head.val)),
        any ||| (localWords[position]! ^^^ leWord head.val))) := by
  rw [difference.default_loop.body, next_live _ _ _ _ _ _ leftBound rightBound, bind_ok]
  dsimp! only
  rw [try_from_exact head full, bind_ok]
  simp only [core.result.Result.expect, lift, bind_ok,
    Slice.Inhabited_getElem_eq_getElem! localWords position rightBound, leWord,
    dite_eq_left (show head.val.length = (8#usize).val from full)]

private theorem step_done (destination localWords : Slice U64) (position : Nat)
    (remainder : Slice U8) (back : Back) (any : U64) :
    difference.default_loop.body (stateAt destination localWords position [] remainder) back any =
      .ok (.done (any, back (stateAt destination localWords position [] remainder))) := by
  simp only [difference.default_loop.body, next, stateAt, bind_ok]
  rfl

private theorem scan (destination localWords : Slice U64) (chunks : List (Slice U8))
    (remainder : Slice U8) (position : Nat) (any : U64) (back : Back)
    (lengths : destination.length = localWords.length)
    (cover : position + chunks.length = destination.length)
    (full : ∀ bytes ∈ chunks, bytes.length = 8) :
    difference.default_loop (stateAt destination localWords position chunks remainder) back any =
      .ok ((wordsFrom localWords position (chunks.map Slice.val)).foldl (· ||| ·) any,
        back (stateAt (writeFrom destination position (wordsFrom localWords position (chunks.map Slice.val)))
          localWords destination.length [] remainder)) := by
  induction chunks generalizing position any back with
  | nil =>
    have index : position = destination.length := by simpa using cover
    unfold difference.default_loop
    rw [loop]
    dsimp only
    rw [step_done, bind_ok]
    simp only [List.map_nil, wordsFrom, List.foldl_nil, writeFrom, index]
  | cons head rest ih =>
    have active : position < destination.length := by simp only [List.length_cons] at cover; omega
    have tailCover : position + 1 + rest.length = destination.length := by
      simp only [List.length_cons] at cover
      omega
    unfold difference.default_loop
    rw [loop]
    dsimp only
    rw [step_live _ _ _ _ _ _ active (lengths ▸ active) (full head (by simp)), bind_ok]
    change difference.default_loop _ _ _ = _
    rw [ih _ _ _ tailCover (fun bytes member => full bytes (List.mem_cons_of_mem head member))]
    rfl

abbrev byteGroups (bytes : List U8) : List (List U8) :=
  (List.toChunksExact 8 (by decide) bytes).1

private theorem byteGroups_partition (bytes : List U8) (count : Nat)
    (exactBytes : bytes.length = 8 * count) :
    (byteGroups bytes).length = count ∧
      (∀ chunk ∈ byteGroups bytes, chunk.length = 8) ∧
      (List.toChunksExact 8 (by decide) bytes).2 = [] := by
  induction count generalizing bytes with
  | zero =>
    have empty : bytes = [] := List.length_eq_zero_iff.mp (by simpa using exactBytes)
    subst bytes
    simp [byteGroups, List.toChunksExact]
  | succ count ih =>
    have long : 8 ≤ bytes.length := by omega
    have rest : (bytes.drop 8).length = 8 * count := by simp [List.length_drop]; omega
    obtain ⟨countEq, full, empty⟩ := ih (bytes.drop 8) rest
    have split : List.toChunksExact 8 (by decide) bytes =
        (bytes.take 8 :: byteGroups (bytes.drop 8), (List.toChunksExact 8 (by decide) (bytes.drop 8)).2) := by
      rw [List.toChunksExact, dite_eq_right (Nat.not_lt.mpr long)]
    change (List.toChunksExact 8 (by decide) bytes).1.length = count + 1 ∧
      (∀ chunk ∈ (List.toChunksExact 8 (by decide) bytes).1, chunk.length = 8) ∧
      (List.toChunksExact 8 (by decide) bytes).2 = []
    rw [split]
    simp only [List.length_cons, countEq, List.mem_cons, empty, and_true]
    refine ⟨trivial, ?_⟩
    intro chunk member
    rcases member with rfl | later
    · simp [List.length_take, Nat.min_eq_left long]
    · exact full chunk later

private theorem chunks_materialized (remote : Slice U8) :
    ∃ iterator : ByteChunks, core.slice.Slice.chunks_exact remote 8#usize = .ok iterator ∧
      iterator.chunks.map Slice.val = byteGroups remote.val := by
  unfold core.slice.Slice.chunks_exact
  rw [dite_eq_left (show 0 < (8#usize).val from by decide)]
  refine ⟨_, rfl, ?_⟩
  dsimp only
  rw [List.map_map]
  simp only [Function.comp_def, Slice.from_val]
  exact List.attach_map_subtype_val _

private theorem lengths_eq (left : Slice U64) (right : Slice U64) :
    left.len = right.len ↔ left.length = right.length := by
  constructor
  · intro same
    simpa using congrArg UScalar.val same
  · intro same
    exact UScalar.eq_of_val_eq (by simpa using same)

private theorem byte_length_product (destination : Slice U64)
    (fits : 8 * destination.length ≤ Usize.max) :
    ∃ count : Usize, (8#usize * destination.len : Result Usize) = .ok count ∧ count.val = 8 * destination.length := by
  have bound : (8#usize).val * destination.len.val ≤ UScalar.max UScalarTy.Usize := by simpa [UScalar.max_USize_eq] using fits
  obtain ⟨count, result, spec⟩ := RawMulTable.normal_of_spec _ _ (UScalar.mul_spec (x := 8#usize) (y := destination.len) bound)
  exact ⟨count, result, by simpa using spec⟩

private theorem or_eq_zero (a b : U64) : a ||| b = 0#u64 ↔ a = 0#u64 ∧ b = 0#u64 := by
  simp only [UScalar.eq_equiv_bv_eq, UScalar.bv_or]
  change a.bv ||| b.bv = 0 ↔ a.bv = 0 ∧ b.bv = 0
  bv_decide

private theorem fold_eq_zero (words : List U64) (initial : U64) :
    words.foldl (· ||| ·) initial = 0#u64 ↔ initial = 0#u64 ∧ ∀ word ∈ words, word = 0#u64 := by
  induction words generalizing initial with
  | nil => simp
  | cons word rest ih =>
    simp only [List.foldl_cons, ih, or_eq_zero, List.forall_mem_cons, and_assoc]

private theorem flag_refines (words : List U64) :
    (words.foldl (· ||| ·) 0#u64 != 0#u64) = true ↔ ∃ word ∈ words, word ≠ 0#u64 := by
  rw [bne_iff_ne]
  constructor
  · intro nonzero
    by_contra absent
    apply nonzero
    refine (fold_eq_zero words 0#u64).mpr ⟨rfl, ?_⟩
    intro word member
    by_contra changed
    exact absent ⟨word, member, changed⟩
  · rintro ⟨word, member, changed⟩ zero
    exact changed (((fold_eq_zero words 0#u64).mp zero).2 word member)

private theorem writeFrom_all (destination : Slice U64) (words : List U64)
    (size : words.length = destination.length) :
    (writeFrom destination 0 words).val = words := by
  apply List.ext_getElem
  · change (writeFrom destination 0 words).length = words.length
    rw [writeFrom_length, size]
  · intro index outBound wordBound
    have word := writeFrom_word destination 0 words (by rw [Nat.zero_add, size]) index wordBound
    simpa only [Nat.zero_add, Slice.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ outBound] using word

/-- The original default returns the word-wise XOR against complete
little-endian groups and a Boolean indicating whether any output word differs. -/
def ActualDefaultWireDifference : Prop :=
  ∀ (Self F : Type) (destination localWords : Slice U64) (remote : Slice U8),
    destination.length = localWords.length →
    remote.length = 8 * destination.length →
    ∃ (different : Bool) (output : Slice U64),
      difference.default Self F destination localWords remote = .ok (different, output) ∧
      output.val = wordsFrom localWords 0 (byteGroups remote.val) ∧
      (different = true ↔ ∃ word ∈ output.val, word ≠ 0#u64)

theorem default_wire_difference : ActualDefaultWireDifference := by
  intro Self F destination localWords remote lengths bytes
  have fits : 8 * destination.length ≤ Usize.max := by rw [← bytes]; exact remote.length_ineq
  obtain ⟨count, countResult, countEq⟩ := byte_length_product destination fits
  have exactGuard : remote.len = count := by
    apply UScalar.eq_of_val_eq
    simpa only [Slice.len_val, countEq] using bytes
  obtain ⟨iterator, iteratorResult, groups⟩ := chunks_materialized remote
  obtain ⟨chunkCount, chunkLength, _⟩ := byteGroups_partition remote.val destination.length bytes
  have cover : 0 + iterator.chunks.length = destination.length := by
    rw [← List.length_map (f := Slice.val) («as» := iterator.chunks), groups, chunkCount, Nat.zero_add]
  have full : ∀ chunk ∈ iterator.chunks, chunk.length = 8 := by
    intro chunk member
    exact chunkLength chunk.val (groups ▸ List.mem_map_of_mem member)
  have scanned := scan destination localWords iterator.chunks iterator.remainder 0 0#u64 id lengths cover full
  rw [groups] at scanned
  have wordsCount : (wordsFrom localWords 0 (byteGroups remote.val)).length = destination.length := by
    rw [wordsFrom_length, chunkCount]
  refine ⟨(wordsFrom localWords 0 (byteGroups remote.val)).foldl (· ||| ·) 0#u64 != 0#u64,
    writeFrom destination 0 (wordsFrom localWords 0 (byteGroups remote.val)),
    ?_, writeFrom_all _ _ wordsCount, ?_⟩
  · unfold difference.default
    rw [ite_eq_left ((lengths_eq _ _).mpr lengths)]
    dsimp only
    rw [countResult, bind_ok, ite_eq_left exactGuard]
    simp only [core.slice.Slice.iter_mut, zip,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
      iteratorResult, core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_ok]
    dsimp! only
    change Aeneas.Std.bind
      (difference.default_loop (stateAt destination localWords 0 iterator.chunks iterator.remainder) id 0#u64)
      (fun (any, restored) => Result.ok (any != 0#u64, restored.fst.fst.slice)) = _
    rw [scanned]
    exact bind_ok _ _
  · rw [writeFrom_all _ _ wordsCount]
    exact flag_refines _

/-- Both original assertion guards reject before entering the iterator.
The byte-length guard applies when the source's checked size product fits. -/
def ActualDefaultWireDifferenceGuards : Prop :=
  ∀ (Self F : Type) (destination localWords : Slice U64) (remote : Slice U8),
    (destination.length ≠ localWords.length →
      difference.default Self F destination localWords remote = .fail .panic) ∧
    (destination.length = localWords.length →
      8 * destination.length ≤ Usize.max →
      remote.length ≠ 8 * destination.length →
      difference.default Self F destination localWords remote = .fail .panic)

theorem default_wire_difference_guards : ActualDefaultWireDifferenceGuards := by
  intro Self F destination localWords remote
  constructor
  · intro lengths
    unfold difference.default
    rw [ite_eq_right (fun eq => lengths ((lengths_eq _ _).mp eq))]
    simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)
  · intro lengths fits bytes
    obtain ⟨count, countResult, countEq⟩ := byte_length_product destination fits
    have different : remote.len ≠ count := by
      intro equal
      have value := congrArg UScalar.val equal
      exact bytes (by simpa only [Slice.len_val, countEq] using value)
    unfold difference.default
    rw [ite_eq_left ((lengths_eq _ _).mpr lengths)]
    dsimp only
    rw [countResult, bind_ok, ite_eq_right different]
    simp only [core.fmt.Arguments.from_str]
    exact bind_ok (() : core.fmt.Arguments) (fun _ => Result.fail Error.panic)

#print axioms default_wire_difference
#print axioms default_wire_difference_guards

end BulksketchBridge.DefaultWireDifference
