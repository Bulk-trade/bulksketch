import BulksketchBridge.RebuiltLocatorLoop
import BulksketchBridge.Square

namespace BulksketchBridge.RebuiltLfsr

open Aeneas Aeneas.Std
open bulksketch.decode.verify

abbrev MutIterator := core.slice.iter.IterMut U64

@[simp] theorem square_length (words : Slice U64) (start : Nat) :
    (squareFrom words start).length = words.length := by simp [squareFrom, Slice.length]

theorem square_word (words : Slice U64) (start index : Nat) (bound : index < words.length) :
    (squareFrom words start)[index]! =
      if start ≤ index then Square.expectedWord words[index]! else words[index]! := by
  simp only [squareFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ index (by simpa using bound), List.getElem_ofFn]

private theorem square_done (words : Slice U64) : squareFrom words words.length = words := by
  apply Slice.ext_getElem (by simp)
  intro index outBound bound
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ outBound, Slice.Inhabited_getElem_eq_getElem! _ _ bound,
    square_word words words.length index bound, ite_eq_right (by omega)]

private theorem square_replace (words : Slice U64) (index : Nat) (active : index < words.length) :
    (squareFrom words (index + 1)).setAtNat index (Square.expectedWord words[index]!) =
      squareFrom words index := by
  apply Slice.ext_getElem (by simp)
  intro j updatedBound outputBound
  have bounded : j < words.length := by simpa using outputBound
  rw [Slice.Inhabited_getElem_eq_getElem! _ j updatedBound,
    Slice.Inhabited_getElem_eq_getElem! _ j outputBound, square_word words index j bounded,
    Slice.getElem!_Nat_eq]
  by_cases same : index = j
  · subst j
    rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa), ite_eq_left (Nat.le_refl _)]
  · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same, ← Slice.getElem!_Nat_eq,
      square_word words (index + 1) j bounded]
    have sameGuard : (index + 1 ≤ j) ↔ (index ≤ j) := by omega
    simp only [sameGuard]

private theorem mutable_next (words : Slice U64) (index : Nat) (active : index < words.length) :
    core.slice.iter.IteratorIterMut.next (⟨words, index⟩ : MutIterator) =
      Result.ok (some words[index]!, ⟨words, index + 1⟩,
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat index value }) := by
  have lengthGuard : index < words.len.val := by simpa using active
  have exactStep : core.slice.iter.IteratorIterMut.next (⟨words, index⟩ : MutIterator) =
      Result.ok (some (words[index]'active), ⟨words, index + 1⟩,
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat index value }) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · dsimp only
      congr 3
      funext later replacement
      cases replacement <;> rfl
    · rename_i stop
      exact False.elim (stop lengthGuard)
  exact exactStep.trans (congrArg (fun value => Result.ok
    (some value, (⟨words, index + 1⟩ : MutIterator),
      fun (later : MutIterator) (replacement : Option U64) => match replacement with
        | none => later
        | some value => { later with slice := later.slice.setAtNat index value }))
    (Slice.Inhabited_getElem_eq_getElem! words index active))

private theorem mutable_done (words : Slice U64) :
    core.slice.iter.IteratorIterMut.next (⟨words, words.length⟩ : MutIterator) =
      Result.ok (none, ⟨words, words.length⟩, fun later _ => later) := by
  unfold core.slice.iter.IteratorIterMut.next
  have stop : ¬ (⟨words, words.length⟩ : MutIterator).i < words.len.val := by simp
  rw [dite_eq_right stop]

theorem square_loop {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (square : squaringLaw kernels) (words : Slice U64) (index count : Nat)
    (remaining : index + count = words.length) (back : MutIterator → MutIterator) :
    ∃ finish : MutIterator → MutIterator,
      rebuilt_lfsr_loop1 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
        ⟨words, index⟩ back = Result.ok (⟨words, words.length⟩, finish) ∧
      finish ⟨words, words.length⟩ = back ⟨squareFrom words index, words.length⟩ := by
  induction count generalizing index back with
  | zero =>
    have terminal : index = words.length := by omega
    subst index
    refine ⟨fun state => back state, ?_, ?_⟩
    · unfold rebuilt_lfsr_loop1 loop
      dsimp only
      simp only [rebuilt_lfsr_loop1.body, mutable_done, bind_ok]
      dsimp! only
      simp only [bind_ok]
    · rw [square_done]
  | succ count ih =>
    have active : index < words.length := by omega
    let update (state : MutIterator) := back { state with
      slice := state.slice.setAtNat index (Square.expectedWord words[index]!) }
    obtain ⟨finish, next, composed⟩ := ih (index + 1) (by omega) update
    refine ⟨finish, ?_, ?_⟩
    · unfold rebuilt_lfsr_loop1 loop
      dsimp only
      simp only [rebuilt_lfsr_loop1.body, mutable_next words index active, bind_ok]
      dsimp! only
      try simp only [square words[index]!, Square.square_refines, bind_ok]
      try dsimp! only
      try simp only [bind_ok]
      change rebuilt_lfsr_loop1 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels
        ⟨words, index + 1⟩ update = _
      exact next
    · rw [composed]
      simp only [update, square_replace words index active]

end BulksketchBridge.RebuiltLfsr
