import BulksketchBridge.RowLocalInner

namespace BulksketchBridge.CandidateNormalization

open Aeneas.Std
open bulksketch.sketch.candidates

private theorem row_slice_succ (words : List U64) (base index : Nat)
    (lower : base ≤ index) (active : index < words.length) :
    words.slice base (index + 1) = words.slice base index ++ [words[index]!] := by
  have inside : index - base < (words.drop base).length := by rw [List.length_drop]; omega
  unfold List.slice
  rw [show index + 1 - base = index - base + 1 by omega, List.take_succ_eq_append_getElem inside,
    List.getElem_drop]
  simp only [Nat.add_sub_of_le lower, List.Inhabited_getElem_eq_getElem! _ _ active]

private theorem row_slice_last (words : Slice U64) (base used : Nat) (kept : List U64)
    (lower : base ≤ used) (room : used ≤ words.length) (prefixEq : words.val.slice base used = kept.reverse)
    (word : U64) :
    kept.head? = some word ↔ used ≠ base ∧ words[used - 1]! = word := by
  by_cases empty : used = base
  · have nothing : kept.reverse = [] := by rw [← prefixEq, empty]; simp [List.slice]
    have noKept := List.reverse_eq_nil_iff.mp nothing
    simp [empty, noKept]
  · have active : base < used := by omega
    have prevRoom : used - 1 < words.val.length := by change used - 1 < words.length; omega
    have rev : (words.val.slice base used).reverse = kept := by rw [prefixEq, List.reverse_reverse]
    have last : kept.head? = some words[used - 1]! := by
      have fits : used ≤ words.val.length := room
      rw [← rev, ← List.getLast?_eq_head?_reverse, List.getLast?_eq_getElem?, List.slice_length,
        Nat.min_eq_right (Nat.sub_le_sub_right fits base)]
      unfold List.slice
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop,
        show base + (used - base - 1) = used - 1 by omega, List.getElem?_eq_getElem prevRoom,
        Slice.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ prevRoom]
    simp only [last, Option.some.injEq]
    exact ⟨fun equal => ⟨empty, equal⟩, And.right⟩

private theorem slice_matches (before after : Slice U64) (base stop : Nat)
    (fitsBefore : stop ≤ before.length) (fitsAfter : stop ≤ after.length)
    (same : ∀ index, base ≤ index → index < stop → after[index]! = before[index]!) :
    after.val.slice base stop = before.val.slice base stop := by
  have beforeLen : (before.val.slice base stop).length = stop - base := by
    rw [List.slice_length, Nat.min_eq_right (Nat.sub_le_sub_right fitsBefore _)]
  have afterLen : (after.val.slice base stop).length = stop - base := by
    rw [List.slice_length, Nat.min_eq_right (Nat.sub_le_sub_right fitsAfter _)]
  apply List.ext_getElem (afterLen.trans beforeLen.symm)
  intro index afterRoom beforeRoom
  have inside : base + index < stop := by rw [afterLen] at afterRoom; omega
  rw [List.Inhabited_getElem_eq_getElem! _ _ afterRoom, List.Inhabited_getElem_eq_getElem! _ _ beforeRoom,
    List.getElem!_slice _ _ _ _ ⟨fitsAfter, inside⟩,
    List.getElem!_slice _ _ _ _ ⟨fitsBefore, inside⟩]
  simpa only [Slice.getElem!_Nat_eq] using same (base + index) (by omega) inside

def RowCompactContents (source : Slice U64) (base index : Nat) (state : RowCompactState) : Prop :=
  state.ids.length = source.length ∧ base ≤ state.used ∧ state.used ≤ index ∧
  state.ids.val.slice base state.used = ((source.val.slice base index).foldl compactStep []).reverse ∧
  ∀ position, (position < base ∨ index ≤ position) → position < source.length →
    state.ids[position]! = source[position]!

private theorem compact_contents_step (source : Slice U64) (base index : Nat) (state : RowCompactState)
    (inside : index < source.length) (holds : RowCompactContents source base index state) :
    RowCompactContents source base (index + 1) (rowCompactAt base index state) := by
  obtain ⟨length, baseUsed, usedIndex, retained, future⟩ := holds
  let kept := (source.val.slice base index).foldl compactStep []
  let word := source[index]!
  have value : state.ids[index]! = word := future index (.inr le_rfl) inside
  have step : (source.val.slice base (index + 1)).foldl compactStep [] = compactStep kept word := by
    rw [row_slice_succ _ _ _ (baseUsed.trans usedIndex) inside]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, kept, word, Slice.getElem!_Nat_eq]
  have headGuard := row_slice_last state.ids base state.used kept baseUsed (by omega) retained word
  by_cases skip : word = 0#u64 ∨ kept.head? = some word
  · have unchanged : rowCompactAt base index state = state := by
      unfold rowCompactAt
      rw [value]
      exact ite_eq_left (skip.imp (fun h => h) headGuard.mp)
    rw [unchanged]
    refine ⟨length, baseUsed, by omega, ?_, ?_⟩
    · rw [step, compactStep, ite_eq_left skip]
      exact retained
    · intro position kept inside
      exact future position (kept.imp (fun h => h) (by omega)) inside
  · let written := state.ids.setAtNat state.used word
    have inserted : rowCompactAt base index state = ⟨written, state.used + 1⟩ := by
      unfold rowCompactAt
      rw [value]
      exact ite_eq_right (fun rejected => skip (rejected.imp (fun h => h) headGuard.mpr))
    have writtenLen : written.length = source.length :=
      (Slice.setAtNat_length _ _ _).trans length
    have unchanged (position : Nat) (different : state.used ≠ position) :
        written[position]! = state.ids[position]! := by
      simp only [written, Slice.getElem!_Nat_eq]
      exact Slice.getElem!_Nat_setAtNat_ne _ _ _ _ different
    have before : written.val.slice base state.used = state.ids.val.slice base state.used :=
      slice_matches state.ids written base state.used (by omega) (by omega) (fun i _ hi => unchanged i (by omega))
    have copied : written[state.used]! = word := by
      simp only [written, Slice.getElem!_Nat_eq]
      exact Slice.getElem!_Nat_setAtNat_eq _ _ _ (by omega)
    rw [inserted]
    refine ⟨writtenLen, by change base ≤ state.used + 1; omega,
      by change state.used + 1 ≤ index + 1; omega, ?_, ?_⟩
    · change written.val.slice base (state.used + 1) = _
      rw [row_slice_succ _ _ _ baseUsed (by change state.used < written.length; omega),
        ← Slice.getElem!_Nat_eq, before, copied, retained, step, compactStep, ite_eq_right skip,
        List.reverse_cons]
    · intro position safe room
      exact (unchanged position (by rcases safe <;> omega)).trans (future position (safe.imp (fun h => h) (by omega)) room)

theorem row_compact_contents (source : Slice U64) (base index fuel : Nat) (state : RowCompactState)
    (room : index + fuel ≤ source.length) (holds : RowCompactContents source base index state) :
    RowCompactContents source base (index + fuel) (rowCompactFrom base fuel index state) := by
  induction fuel generalizing index state with
  | zero => simpa only [rowCompactFrom, Nat.add_zero] using holds
  | succ fuel ih =>
    have next := compact_contents_step source base index state (by omega) holds
    have result := ih (index + 1) (rowCompactAt base index state) (by omega) next
    simpa only [rowCompactFrom, show index + 1 + fuel = index + (fuel + 1) by omega] using result

/-- The actual inner call compacts only the source row's interval. Its
returned count and exact retained word slice agree with the unsigned model. -/
def ActualNativeRowLocalCompactedSlice : Prop :=
  ∀ (ids : Slice U64) (base stop : Usize), base.val ≤ stop.val → stop.val ≤ ids.length →
    ∃ written used,
      normalize_rows_loop0_loop0 ⟨base, stop⟩ ids base base = .ok (written, used) ∧
      written.length = ids.length ∧ base.val ≤ used.val ∧ used.val ≤ stop.val ∧
      written.val.slice base.val used.val = compactedWords (ids.val.slice base.val stop.val) ∧
      written.val.take base.val = ids.val.take base.val

theorem native_row_local_compacted_slice : ActualNativeRowLocalCompactedSlice := by
  intro ids base stop ordered fits
  let initial : RowCompactState := ⟨ids, base.val⟩
  let out := rowCompactFrom base.val (stop.val - base.val) base.val initial
  have init : RowCompactContents ids base.val base.val initial := by
    refine ⟨rfl, le_rfl, le_rfl, ?_, by intros; rfl⟩
    simp [initial, List.slice]
  have consumed := row_compact_contents ids base.val base.val (stop.val - base.val) initial
    (by rw [Nat.add_sub_of_le ordered]; exact fits) init
  rw [Nat.add_sub_of_le ordered] at consumed
  obtain ⟨used, native, usedVal, length, lower, upper⟩ :=
    native_row_local_compact base ⟨base, stop⟩ ids base le_rfl le_rfl ordered fits
  change used.val = out.used at usedVal
  refine ⟨out.ids, used, native, length, ?_, ?_, ?_, ?_⟩
  · rw [usedVal]; exact lower
  · rw [usedVal]; exact upper
  · rw [usedVal]; exact consumed.2.2.2.1
  · have before := slice_matches ids out.ids 0 base.val (by omega)
      (by rw [show out.ids.length = ids.length from consumed.1]; exact ordered.trans fits) (fun index _ h => consumed.2.2.2.2 index (.inl h) (by omega))
    simpa only [List.slice, List.drop_zero, Nat.sub_zero] using before

#print axioms native_row_local_compacted_slice

end BulksketchBridge.CandidateNormalization
