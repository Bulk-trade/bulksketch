import Arithmetic.SliceKernelTypes

namespace BulksketchBridge.DenseCoefficient

open Aeneas Aeneas.Std

/-- The source extends the active window only as far as the edited coefficient. -/
def activeSize (length index : Nat) : Nat := max length (index + 1)

/-- A complete post-state description. The selected coefficient is XORed
against its old value inside the original active window and against zero
outside it. The remaining new coefficients are cleared. -/
def expectedCoefficient (original : Slice U64) (length index : Nat) (value : U64)
    (slot : Nat) : U64 :=
  if slot = index then
    (if index < length then original[index]! else 0#u64) ^^^ value
  else if length ≤ slot ∧ slot < activeSize length index then 0#u64
  else original[slot]!

theorem clear_window (original : Slice U64) (start stop slot : Nat)
    (ordered : start ≤ stop) (valid : slot < original.length) :
    (original.setSlice! start (List.replicate (stop - start) 0#u64))[slot]! =
      if start ≤ slot ∧ slot < stop then 0#u64 else original[slot]! := by
  by_cases before : slot < start
  · rw [ite_eq_right (by omega), Slice.setSlice!_getElem!_prefix _ _ _ _ before]
  · by_cases inside : slot < stop
    · rw [ite_eq_left (by omega), Slice.setSlice!_getElem!_middle _ _ _ _]
      · have bounded : slot - start < stop - start := by omega
        simp only [List.getElem!_eq_getElem?_getD, List.getElem?_replicate, bounded,
          ite_true, Option.getD_some]
      · simp only [List.length_replicate]
        omega
    · rw [ite_eq_right (by omega), Slice.setSlice!_getElem!_suffix _ _ _ _]
      simp only [List.length_replicate]
      omega

/-- The frame covers every original slot, including any inactive tail beyond
the newly computed active size. -/
theorem coefficient_frame (original filled result : Slice U64) (length index : Usize)
    (value current : U64) (indexBound : index.val < original.length)
    (cleared : filled = original.setSlice! length.val
      (List.replicate (activeSize length.val index.val - length.val) 0#u64))
    (read : current = filled[index.val]!)
    (updated : result = filled.set index (current ^^^ value)) :
    result.length = original.length ∧
      ∀ slot, slot < original.length →
        result[slot]! = expectedCoefficient original length.val index.val value slot := by
  have filledLength : filled.length = original.length := by rw [cleared, Slice.setSlice!_length]
  refine ⟨by rw [updated, Slice.set_length, filledLength], ?_⟩
  intro slot valid
  have ordered : length.val ≤ activeSize length.val index.val := Nat.le_max_left _ _
  have indexInside : index.val < activeSize length.val index.val := by
    exact Nat.lt_of_succ_le (Nat.le_max_right length.val (index.val + 1))
  by_cases selected : slot = index.val
  · subst slot
    rw [updated, Slice.getElem!_Nat_set_eq _ _ _ _ ⟨rfl, by omega⟩, read, cleared,
      clear_window _ _ _ _ ordered indexBound]
    unfold expectedCoefficient
    by_cases earlier : index.val < length.val
    · simp [earlier, show ¬(length.val ≤ index.val ∧ index.val < activeSize length.val index.val) by omega]
    · simp [earlier, indexInside, show length.val ≤ index.val by omega]
  · rw [updated, Slice.getElem!_Nat_set_ne _ _ _ _ (Ne.symm selected), cleared,
      clear_window _ _ _ _ ordered valid]
    simp only [expectedCoefficient, selected, ite_false]

end BulksketchBridge.DenseCoefficient
