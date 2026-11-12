import BulksketchBridge.PortableEncodingChallenges
import BulksketchBridge.Portable

namespace BulksketchBridge.PortableEncoding

open Aeneas Aeneas.Std
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

abbrev MutIter := core.slice.iter.IterMut U64

private theorem mutable_next (iterator : MutIter) (bounded : iterator.i < iterator.slice.length) :
    core.slice.iter.IteratorIterMut.next iterator =
      Result.ok (some iterator.slice[iterator.i]!, { iterator with i := iterator.i + 1 },
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat iterator.i value }) := by
  have lengthGuard : iterator.i < iterator.slice.len.val := by simpa using bounded
  have step : core.slice.iter.IteratorIterMut.next iterator =
      Result.ok (some (iterator.slice[iterator.i]'bounded), { iterator with i := iterator.i + 1 },
        fun later replacement => match replacement with
          | none => later
          | some value => { later with slice := later.slice.setAtNat iterator.i value }) := by
    unfold core.slice.iter.IteratorIterMut.next
    split
    · dsimp only
      congr 3
      funext later replacement
      cases replacement <;> rfl
    · contradiction
  rw [step, Slice.Inhabited_getElem_eq_getElem! iterator.slice iterator.i bounded]

private theorem mutable_done (iterator : MutIter) (exhausted : iterator.slice.length ≤ iterator.i) :
    core.slice.iter.IteratorIterMut.next iterator = Result.ok (none, iterator, fun later _ => later) := by
  have stopped : ¬ iterator.i < iterator.slice.len.val := by simpa using Nat.not_lt.mpr exhausted
  unfold core.slice.iter.IteratorIterMut.next
  split
  · contradiction
  · rfl

theorem shared_next (slice : Slice U64) (i : Nat) (bounded : i < slice.length) :
    core.slice.iter.IteratorSliceIter.next (⟨slice, i⟩ : core.slice.iter.Iter U64) =
      Result.ok (some slice[i]!, ⟨slice, i + 1⟩) := by
  have lengthGuard : i < slice.len.val := by simpa using bounded
  have step : core.slice.iter.IteratorSliceIter.next (⟨slice, i⟩ : core.slice.iter.Iter U64) =
      Result.ok (some (slice[i]'bounded), ⟨slice, i + 1⟩) := by
    unfold core.slice.iter.IteratorSliceIter.next
    split
    · rfl
    · contradiction
  rw [step, Slice.Inhabited_getElem_eq_getElem! slice i bounded]

theorem shared_done (slice : Slice U64) (i : Nat) (exhausted : slice.length ≤ i) :
    core.slice.iter.IteratorSliceIter.next (⟨slice, i⟩ : core.slice.iter.Iter U64) =
      Result.ok (none, ⟨slice, i⟩) := by
  have stopped : ¬ i < slice.len.val := by simpa using Nat.not_lt.mpr exhausted
  unfold core.slice.iter.IteratorSliceIter.next
  split
  · contradiction
  · rfl

theorem foldColumn_drop_step (ids : Slice U64) (i slot : Nat) (initial : U64)
    (active : i < ids.length) :
    foldColumn (ids.val.drop i) slot initial =
      foldColumn (ids.val.drop (i + 1)) slot (initial ^^^ oddPower ids[i]! slot) := by
  rw [List.drop_eq_getElem_cons (show i < ids.val.length from active)]
  simp only [foldColumn, List.foldl_cons, Slice.getElem!_Nat_eq]
  rw [List.Inhabited_getElem_eq_getElem! _ i active]

def updateFrom (slice : Slice U64) (square power : U64) (start : Nat) : Slice U64 :=
  Slice.from (List.ofFn fun j : Fin slice.length =>
    if start ≤ j.val then slice[j.val]! ^^^ powerFrom square power (j.val + 1 - start)
    else slice[j.val]!) (by simp)

@[simp] theorem updateFrom_length (slice : Slice U64) (square power : U64) (start : Nat) :
    (updateFrom slice square power start).length = slice.length := by simp [updateFrom]

theorem updateFrom_word (slice : Slice U64) (square power : U64) (start j : Nat)
    (bounded : j < slice.length) :
    (updateFrom slice square power start)[j]! =
      if start ≤ j then slice[j]! ^^^ powerFrom square power (j + 1 - start) else slice[j]! := by
  simp only [updateFrom, Slice.getElem!_Nat_eq, Slice.from_val]
  rw [← List.Inhabited_getElem_eq_getElem! _ j (by simpa using bounded), List.getElem_ofFn]

private theorem power_step (square power : U64) (count : Nat) :
    powerFrom square (wordMul power square) count = powerFrom square power (count + 1) := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [powerFrom, ih]

private theorem update_done (slice : Slice U64) (square power : U64) :
    updateFrom slice square power slice.length = slice := by
  apply Slice.ext_getElem (by simp)
  intro j updatedBound bound
  rw [Slice.Inhabited_getElem_eq_getElem! _ j updatedBound,
    Slice.Inhabited_getElem_eq_getElem! slice j bound,
    updateFrom_word slice square power _ j bound, ite_eq_right (by omega)]

private theorem update_step (slice : Slice U64) (square power : U64) (i : Nat)
    (bounded : i < slice.length) :
    (updateFrom slice square (wordMul power square) (i + 1)).setAtNat i
        (slice[i]! ^^^ wordMul power square) = updateFrom slice square power i := by
  apply Slice.ext_getElem (by simp)
  intro j updatedBound outputBound
  have jBound : j < slice.length := by simpa using outputBound
  rw [Slice.Inhabited_getElem_eq_getElem! _ j updatedBound,
    Slice.Inhabited_getElem_eq_getElem! _ j outputBound,
    updateFrom_word slice square power i j jBound, Slice.getElem!_Nat_eq]
  by_cases same : i = j
  · subst j
    rw [Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa using bounded), ite_eq_left (Nat.le_refl _),
      show i + 1 - i = 1 by omega]
    rfl
  · rw [Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same, ← Slice.getElem!_Nat_eq,
      updateFrom_word slice square (wordMul power square) (i + 1) j jBound]
    by_cases later : i + 1 ≤ j
    · rw [ite_eq_left later, ite_eq_left (by omega), power_step]
      congr 2
      omega
    · rw [ite_eq_right later, ite_eq_right (by omega)]

private def replace (later : MutIter) (i : Nat) (value : U64) : MutIter :=
  { later with slice := later.slice.setAtNat i value }

private theorem body_step (slice : Slice U64) (square power : U64) (i : Nat)
    (bounded : i < slice.length) (back : MutIter → MutIter) :
    insert_nonzero_loop0_loop0.body bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
      square ⟨slice, i⟩ back power = Result.ok (ControlFlow.cont
        (⟨slice, i + 1⟩, fun later => back (replace later i (slice[i]! ^^^ wordMul power square)),
          wordMul power square)) := by
  have step := mutable_next (⟨slice, i⟩ : MutIter) bounded
  simp only [insert_nonzero_loop0_loop0.body, step, bind_ok]
  dsimp! only
  simp only [(Portable.mul_refines power square).1, wordMul, bind_ok, lift, replace]

private theorem body_done (slice : Slice U64) (square power : U64) (back : MutIter → MutIter) :
    insert_nonzero_loop0_loop0.body bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
      square ⟨slice, slice.length⟩ back power =
      Result.ok (ControlFlow.done (⟨slice, slice.length⟩, back)) := by
  have done := mutable_done (⟨slice, slice.length⟩ : MutIter) (Nat.le_refl _)
  simp only [insert_nonzero_loop0_loop0.body, done, bind_ok]
  dsimp! only

/-- Compose the original loop's deferred writes, retaining its final iterator
and the caller-supplied restoration. -/
theorem successors_loop_refines (slice : Slice U64) (square power : U64)
    (start : Nat) (bounded : start ≤ slice.length) (back : MutIter → MutIter) :
    ∃ (final : MutIter) (restore : MutIter → MutIter),
      insert_nonzero_loop0_loop0 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        ⟨slice, start⟩ back square power = Result.ok (final, restore) ∧
      restore final = back ⟨updateFrom slice square power start, slice.length⟩ := by
  suffices ∀ remaining start, start ≤ slice.length → slice.length - start = remaining →
    ∀ power (back : MutIter → MutIter), ∃ (final : MutIter) (restore : MutIter → MutIter),
      insert_nonzero_loop0_loop0 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        ⟨slice, start⟩ back square power = Result.ok (final, restore) ∧
      restore final = back ⟨updateFrom slice square power start, slice.length⟩
    from this (slice.length - start) start bounded rfl power back
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded eq power back
    by_cases active : start < slice.length
    · obtain ⟨final, restore, normal, updated⟩ := ih (slice.length - (start + 1)) (by omega)
        (start + 1) (by omega) rfl (wordMul power square)
        (fun later => back (replace later start (slice[start]! ^^^ wordMul power square)))
      refine ⟨final, restore, ?_, ?_⟩
      · unfold insert_nonzero_loop0_loop0
        unfold loop
        dsimp only
        rw [body_step slice square power start active back]
        simp only [bind_ok]
        exact normal
      · rw [updated]
        simp only [replace, update_step slice square power start active]
    · have terminal : start = slice.length := by omega
      subst start
      refine ⟨⟨slice, slice.length⟩, back, ?_, ?_⟩
      · unfold insert_nonzero_loop0_loop0
        unfold loop
        dsimp only
        simp only [body_done, bind_ok]
      · rw [update_done]

end BulksketchBridge.PortableEncoding
