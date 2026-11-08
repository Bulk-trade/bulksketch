import BulksketchBridge.BmMutable

namespace BulksketchBridge.BmMutable

open Aeneas.Std

/-- Apply a returned mutable writeback to a slice of the caller's later
state. Values are computed from the original loop input. -/
def patchWords (value : Nat → U64) (start count : Nat) (later : Slice U64) : Slice U64 :=
  writesFrom (fun i state => state.setAtNat i (value i)) start count later

@[simp] theorem patchWords_length (value : Nat → U64) (start count : Nat) (later : Slice U64) :
    (patchWords value start count later).length = later.length := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    change ((patchWords value (start + 1) count later).setAtNat start (value start)).length = _
    rw [Slice.setAtNat_length, ih]

theorem patchWords_word (value : Nat → U64) (start count : Nat) (later : Slice U64)
    (index : Nat) (bounded : index < later.length) :
    (patchWords value start count later)[index]! =
      if start ≤ index ∧ index < start + count then value index else later[index]! := by
  induction count generalizing start with
  | zero =>
    have empty : ¬ (start ≤ index ∧ index < start + 0) := by omega
    simp [patchWords, writesFrom, empty]
  | succ count ih =>
    change ((patchWords value (start + 1) count later).setAtNat start (value start))[index]! = _
    by_cases same : start = index
    · subst index
      rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ (by simpa using bounded)]
      rw [ite_eq_left (by omega)]
    · rw [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same,
        ← Slice.getElem!_Nat_eq, ih]
      have interval : (start + 1 ≤ index ∧ index < start + 1 + count) ↔
          (start ≤ index ∧ index < start + (count + 1)) := by omega
      simp only [interval]

theorem iter_writeback (value : Nat → U64) (start count : Nat) (later : Iter) :
    writesFrom (fun index state => replaceIter state index (value index)) start count later =
      { later with slice := patchWords value start count later.slice } := by
  induction count generalizing start with
  | zero => cases later; rfl
  | succ count ih =>
    rw [writesFrom, ih]
    rfl

theorem zip_writeback (value : Nat → U64) (start count : Nat) (later : Zip) :
    writesFrom (fun index state => MutableZip.replaceLeft state index (value index)) start count later =
      ⟨{ later.fst with slice := patchWords value start count later.fst.slice }, later.snd⟩ := by
  induction count generalizing start with
  | zero => cases later with | mk left right => cases left; rfl
  | succ count ih =>
    rw [writesFrom, ih]
    rfl

/-- The returned BM continuation passes through the shared iterator and both
cursor fields, with exactly the visited left words changed. -/
theorem zipResult_frame (left right : Slice U64) (delta : U64) (start : Nat) (later : Zip) :
    let patched := patchWords (fun index => shiftedWord delta left[index]! right[index]!) start
      (min left.length right.length - start) later.fst.slice
    (zipResult left right delta start id).2 later = ⟨{ later.fst with slice := patched }, later.snd⟩ := by
  apply zip_writeback

end BulksketchBridge.BmMutable
