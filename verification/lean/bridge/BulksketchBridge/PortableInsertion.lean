import BulksketchBridge.PortableInsertionLoop

namespace BulksketchBridge.PortableEncoding

open Aeneas Aeneas.Std
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels

private theorem insert_step (ids : Slice U64) (start : Nat) (active : start < ids.length)
    (first : U64) (successors : Slice U64) :
    insert_nonzero_loop0.body bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
      ⟨ids, start⟩ first successors = Result.ok (ControlFlow.cont
        (⟨ids, start + 1⟩, first ^^^ ids[start]!,
          updateFrom successors (Square.expectedWord ids[start]!) ids[start]! 0)) := by
  obtain ⟨final, restore, innerNormal, innerValue⟩ := successors_loop_refines successors
    (Square.expectedWord ids[start]!) ids[start]! 0 (Nat.zero_le _) (fun iterator => iterator)
  simp only [insert_nonzero_loop0.body, shared_next ids start active, bind_ok]
  dsimp! only
  simp only [lift, (Portable.square_refines ids[start]!).1, bind_ok,
    bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    core.slice.Slice.iter_mut]
  dsimp! only
  simp only [innerNormal, bind_ok]
  dsimp! only
  rw [innerValue]

private theorem insert_done (ids : Slice U64) (first : U64) (successors : Slice U64) :
    insert_nonzero_loop0.body bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
      ⟨ids, ids.length⟩ first successors = Result.ok (ControlFlow.done (first, successors)) := by
  simp only [insert_nonzero_loop0.body, shared_done ids ids.length (Nat.le_refl _), bind_ok]
  dsimp! only

private theorem insertion_loop_refines (ids : Slice U64) (start : Nat) (bounded : start ≤ ids.length)
    (first : U64) (successors : Slice U64) :
    ∃ (head : U64) (tail : Slice U64),
      insert_nonzero_loop0 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        ⟨ids, start⟩ first successors = Result.ok (head, tail) ∧
      head = foldColumn (ids.val.drop start) 0 first ∧ tail.length = successors.length ∧
      ∀ i, i < successors.length → tail[i]! = foldColumn (ids.val.drop start) (i + 1) successors[i]! := by
  suffices ∀ remaining start, start ≤ ids.length → ids.length - start = remaining →
    ∀ first (successors : Slice U64), ∃ (head : U64) (tail : Slice U64),
      insert_nonzero_loop0 bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField
        ⟨ids, start⟩ first successors = Result.ok (head, tail) ∧
      head = foldColumn (ids.val.drop start) 0 first ∧ tail.length = successors.length ∧
      ∀ i, i < successors.length → tail[i]! = foldColumn (ids.val.drop start) (i + 1) successors[i]!
    from this (ids.length - start) start bounded rfl first successors
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro start bounded eq first successors
    by_cases active : start < ids.length
    · obtain ⟨head, tail, normal, headValue, tailLength, tailValues⟩ :=
        ih (ids.length - (start + 1)) (by omega) (start + 1) (by omega) rfl (first ^^^ ids[start]!)
          (updateFrom successors (Square.expectedWord ids[start]!) ids[start]! 0)
      refine ⟨head, tail, ?_, ?_, by simpa using tailLength, ?_⟩
      · unfold insert_nonzero_loop0
        unfold loop
        dsimp only
        rw [insert_step ids start active first successors]
        simp only [bind_ok]
        exact normal
      · rw [headValue, foldColumn_drop_step ids start 0 first active]
        rfl
      · intro i iBound
        rw [tailValues i (by simpa using iBound), foldColumn_drop_step ids start (i + 1) successors[i]! active,
          updateFrom_word successors (Square.expectedWord ids[start]!) ids[start]! 0 i iBound]
        simp only [Nat.zero_le, ite_true, Nat.sub_zero, oddPower]
    · have terminal : start = ids.length := by omega
      subst start
      refine ⟨first, successors, ?_, ?_, rfl, ?_⟩
      · unfold insert_nonzero_loop0
        unfold loop
        dsimp only
        simp only [insert_done, bind_ok]
      · simp [foldColumn]
      · intro i _
        simp [foldColumn]

/-- The original portable kernel adds each odd power into its corresponding
syndrome slot. The empty destination is returned immediately. -/
theorem insert_nonzero_refines : PortableEncodingChallenges.actualInsertNonzeroReturnsFrame := by
  intro odd ids
  cases words : odd.val with
  | nil =>
    have splitExact : bulksketch.core.slice.Slice.split_first_mut odd =
        Result.ok (none, fun _ => odd) := by
      unfold bulksketch.core.slice.Slice.split_first_mut
      split <;> simp_all
    refine ⟨odd, ?_, rfl, ?_⟩
    · simp only [insert_nonzero, splitExact, bind_ok]
      dsimp! only
    · intro i bounded
      have empty : odd.length = 0 := by simp [Slice.length, words]
      omega
  | cons first tail =>
    let successors : Slice U64 := Slice.from tail (by
      have lengthGuard := odd.length_ineq
      rw [words, List.length_cons] at lengthGuard
      omega)
    have splitExact : bulksketch.core.slice.Slice.split_first_mut odd =
        Result.ok (some (first, successors), fun replacement => match replacement with
          | none => odd
          | some (head, tail) => (odd.setSlice! 1 tail.val).setAtNat 0 head) := by
      unfold bulksketch.core.slice.Slice.split_first_mut
      split
      · simp_all
      · rename_i head tail splitWords
        obtain ⟨rfl, rfl⟩ := List.cons.inj (splitWords.symm.trans words)
        dsimp only [successors]
        congr 3
        funext replacement
        cases replacement with
        | none => rfl
        | some pair => cases pair; rfl
    obtain ⟨head, updatedTail, normal, headValue, tailLength, tailValues⟩ :=
      insertion_loop_refines ids 0 (Nat.zero_le _) first successors
    let output := (odd.setSlice! 1 updatedTail.val).setAtNat 0 head
    refine ⟨output, ?_, by simp [output], ?_⟩
    · simp only [insert_nonzero, splitExact, bind_ok]
      dsimp! only
      simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter,
        normal, bind_ok, output]
      dsimp! only
    · have oddLength : odd.length = tail.length + 1 := by simp [Slice.length, words]
      have successorLength : successors.length = tail.length := by simp [successors]
      have updatedLength : updatedTail.val.length = tail.length := tailLength.trans successorLength
      intro slot bounded
      cases slot with
      | zero =>
        have positive : 0 < (odd.setSlice! 1 updatedTail.val).length := by simp; omega
        change ((odd.setSlice! 1 updatedTail.val).setAtNat 0 head)[0]! = _
        rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ positive, headValue]
        simp [Slice.getElem!_Nat_eq, words]
      | succ slot =>
        have slotBound : slot < successors.length := by omega
        have replacedLength : (odd.setSlice! 1 updatedTail.val).length = odd.length := by simp
        rw [show output = (odd.setSlice! 1 updatedTail.val).setAtNat 0 head from rfl,
          Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega),
          ← Slice.getElem!_Nat_eq, Slice.setSlice!_getElem!_middle]
        · simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero, ← Slice.getElem!_Nat_eq]
          rw [tailValues slot slotBound]
          simp [Slice.getElem!_Nat_eq, successors, words]
        · exact ⟨by omega, by rw [updatedLength]; omega, bounded⟩

end BulksketchBridge.PortableEncoding
