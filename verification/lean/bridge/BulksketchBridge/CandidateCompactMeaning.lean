import BulksketchBridge.CandidateCompactNative

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std
open bulksketch.sketch.candidates bulksketch.sketch.shape

/-- The prefix has compacted exactly the consumed input, while every future
read still sees the original ID at its source position. -/
def CompactContents (source : Slice U64) (index : Nat) (state : CompactState) : Prop :=
  state.ids.length = source.length ∧ state.used ≤ index ∧
    state.ids.val.take state.used = ((source.val.take index).foldl compactStep []).reverse ∧
    ∀ position, index ≤ position → position < source.length → state.ids[position]! = source[position]!

private theorem take_written (words : List U64) (atIndex : Nat) (value : U64)
    (inside : atIndex < words.length) :
    (words.set atIndex value).take (atIndex + 1) = words.take atIndex ++ [value] := by
  induction words generalizing atIndex with
  | nil => simp at inside
  | cons head rest ih =>
    cases atIndex with
    | zero => rfl
    | succ atIndex =>
      have active : atIndex < rest.length := by simp only [List.length_cons] at inside; omega
      change head :: (rest.set atIndex value).take (atIndex + 1) = head :: (rest.take atIndex ++ [value])
      rw [ih atIndex active]

private theorem kept_head (ids : Slice U64) (used : Nat) (kept : List U64)
    (room : used ≤ ids.length) (matchPrefix : ids.val.take used = kept.reverse) (id : U64) :
    kept.head? = some id ↔ used ≠ 0 ∧ ids[used - 1]! = id := by
  by_cases empty : used = 0
  · have nothing : kept.reverse = [] := by rw [← matchPrefix, empty, List.take_zero]
    have none : kept = [] := List.reverse_eq_nil_iff.mp nothing
    simp [none, empty]
  · have positive : 0 < used := Nat.pos_of_ne_zero empty
    have prevIn : used - 1 < ids.val.length := by change used - 1 < ids.length; omega
    have reversed : (ids.val.take used).reverse = kept := by rw [matchPrefix, List.reverse_reverse]
    have previous : kept.head? = some ids[used - 1]! := by
      rw [← reversed, ← List.getLast?_eq_head?_reverse, List.getLast?_eq_getElem?,
        List.length_take, Nat.min_eq_left (show used ≤ ids.val.length from room),
        List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem prevIn, Slice.getElem!_Nat_eq,
        List.Inhabited_getElem_eq_getElem! _ _ prevIn]
    simp only [previous, Option.some.injEq]
    exact ⟨fun equal => ⟨empty, equal⟩, And.right⟩

theorem compact_step_contents (buckets index : Nat) (source : Slice U64) (state : CompactState)
    (inside : index < source.length) (invariant : CompactContents source index state) :
    CompactContents source (index + 1) (compactAt buckets index state) := by
  obtain ⟨length, usedBound, retained, rest⟩ := invariant
  let kept := (source.val.take index).foldl compactStep []
  let id := source[index]!
  have idExact : state.ids[index]! = id := rest index le_rfl inside
  have slot : state.used < state.ids.length := by omega
  have nextSource : (source.val.take (index + 1)).foldl compactStep [] = compactStep kept id := by
    have active : index < source.val.length := inside
    rw [List.take_succ_eq_append_getElem active, List.Inhabited_getElem_eq_getElem! _ _ active]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, kept, id, Slice.getElem!_Nat_eq]
  have headGuard := kept_head state.ids state.used kept slot.le retained id
  by_cases skip : id = 0#u64 ∨ kept.head? = some id
  · have stateSame : compactAt buckets index state = state := by
      unfold compactAt
      rw [idExact]
      exact ite_eq_left (skip.imp (fun h => h) headGuard.mp)
    rw [stateSame]
    refine ⟨length, usedBound.trans (Nat.le_succ _), ?_, ?_⟩
    · rw [nextSource, compactStep, ite_eq_left skip]
      exact retained
    · intro position future bounded
      exact rest position (by omega) bounded
  · have stateAppend : compactAt buckets index state = addCompacted buckets state id := by
      unfold compactAt
      rw [idExact]
      exact ite_eq_right (fun rejected => skip (rejected.imp (fun h => h) headGuard.mpr))
    rw [stateAppend]
    refine ⟨?_, by simpa only [addCompacted] using Nat.succ_le_succ usedBound, ?_, ?_⟩
    · simpa only [addCompacted, Slice.setAtNat_length] using length
    · rw [nextSource, compactStep, ite_eq_right skip, List.reverse_cons]
      simp only [addCompacted, Slice.setAtNat, Slice.from_val]
      rw [take_written _ _ _ slot, retained]
    · intro position future bounded
      change (state.ids.setAtNat state.used id)[position]! = source[position]!
      have old : (state.ids.setAtNat state.used id)[position]! = state.ids[position]! := by
        simp only [Slice.getElem!_Nat_eq]
        exact Slice.getElem!_Nat_setAtNat_ne state.ids state.used position id (by omega)
      exact old.trans (rest position (by omega) bounded)

theorem compact_loop_contents (buckets fuel index : Nat) (source : Slice U64) (state : CompactState)
    (inside : index + fuel ≤ source.length) (invariant : CompactContents source index state) :
    CompactContents source (index + fuel) (compactFrom buckets fuel index state) := by
  induction fuel generalizing index state with
  | zero => simpa only [Nat.add_zero, compactFrom] using invariant
  | succ fuel ih =>
    have active : index < source.length := by omega
    have next := compact_step_contents buckets index source state active invariant
    have answer := ih (index + 1) (compactAt buckets index state) (by omega) next
    simpa only [compactFrom, show index + 1 + fuel = index + (fuel + 1) by omega] using answer

/-- From the sorted scratch produced by the merge, the actual native
compaction writes a distinct nonzero prefix with exactly the nonzero input
support. The offset histogram and the untouched workspace remain in the
exact native compaction model. -/
def ActualNativeCandidateCompactDistinct : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F) (offsets ids : Slice U64),
    0 < shape.capacities.length → shape.capacities.length + 1 ≤ offsets.length →
    (∀ slot < offsets.length, offsets[slot]!.val = 0) →
    ids.val.Pairwise (fun a b => bucketKey shape.capacities.length a ≤ bucketKey shape.capacities.length b) →
    let cursor : core.ops.range.Range Usize := ⟨0#usize, ids.len⟩
    ∃ count counts written,
      normalize_loop1 field cursor shape offsets ids 0#usize = .ok (counts, written) ∧
      written.val.take count = compactedWords ids.val ∧
      (written.val.take count).Nodup ∧
      ∀ word, word ∈ written.val.take count ↔ word ∈ ids.val ∧ word ≠ 0#u64

theorem native_candidate_compact_distinct : ActualNativeCandidateCompactDistinct := by
  intro F field shape offsets ids positive room zero sorted
  dsimp only
  let cursor : core.ops.range.Range Usize := ⟨0#usize, ids.len⟩
  let initial : CompactState := ⟨offsets, ids, 0⟩
  have startVal : cursor.start.val = 0 := Usize.ofNatCore_val_eq _
  have endVal : cursor.end.val = ids.length := Slice.len_val _
  have initBounds : CompactBounds shape.capacities.length cursor.start.val
      ⟨offsets, ids, (0#usize).val⟩ := by
    refine ⟨positive, room, by rw [startVal], by rw [startVal]; exact Nat.zero_le _, ?_⟩
    intro slot inside
    rw [zero slot inside]
    exact Nat.zero_le _
  have original : CompactContents ids 0 initial := by
    refine ⟨rfl, le_rfl, rfl, ?_⟩
    intros
    rfl
  have source := (native_candidate_compact field shape cursor offsets ids 0#usize
    (by rw [startVal, endVal]; exact Nat.zero_le _) (by rw [endVal]) initBounds).1
  rw [startVal, endVal, Nat.sub_zero] at source
  let result := compactFrom shape.capacities.length ids.length 0 initial
  have output := compact_loop_contents shape.capacities.length ids.length 0 ids initial (by omega) original
  have words : result.ids.val.take result.used = compactedWords ids.val := by
    unfold compactedWords
    simpa only [Nat.zero_add, Slice.length, List.take_length] using output.2.2.1
  refine ⟨result.used, result.offsets, result.ids, source, words, ?_, ?_⟩
  · rw [words]
    exact compacted_words_distinct _ (bucket_key_injective _) _ sorted
  · intro word
    rw [words]
    exact compacted_words_mem _ _

#print axioms native_candidate_compact_distinct

end BulksketchBridge.CandidateNormalization
