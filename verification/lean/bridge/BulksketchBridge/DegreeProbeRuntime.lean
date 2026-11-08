import Arithmetic.DegreeProbeRuntime
import Arithmetic.MapsRuntime
import BulksketchBridge.RebuiltLocatorLoop
import Mathlib.Data.List.Sort

namespace BulksketchBridge.DegreeProbeRuntime

open Aeneas.Std Aeneas.Std.DegreeProbeRuntime DenseCoefficient RebuiltLfsr

theorem sortedWords_perm (words : Slice U64) : (sortedWords words).val.Perm words.val := by
  rw [sortedWords, Slice.from_val]
  exact List.mergeSort_perm _ _

@[simp] theorem sortedWords_length (words : Slice U64) : (sortedWords words).length = words.length :=
  (sortedWords_perm words).length_eq

theorem sortedWords_ordered (words : Slice U64) : (sortedWords words).val.Pairwise ordered := by
  rw [sortedWords, Slice.from_val]
  have sorted := List.pairwise_mergeSort (le := compareWord)
    (fun left middle right first second => by
      simp only [compareWord, decide_eq_true_eq] at *
      exact Nat.le_trans first second)
    (fun left right => by
      rcases Nat.le_total left.val right.val with less | greater
      · simp [compareWord, less]
      · simp [compareWord, greater])
    words.val
  unfold ordered
  simpa only [compareWord, decide_eq_true_eq] using sorted

/-- Any ascending permutation of unsigned words has exactly the model's
value sequence, including duplicates. This is the value-level standard
library correspondence used at the original `OrdU64` call site. -/
theorem canonical_unique (original result : Slice U64)
    (ascending : result.val.Pairwise ordered) (permutation : result.val.Perm original.val) :
    result = sortedWords original := by
  rw [Slice.eq_iff]
  apply (permutation.trans (sortedWords_perm original).symm).eq_of_pairwise _ ascending (sortedWords_ordered original)
  intro left right _ _ forward backward
  exact UScalar.eq_of_val_eq (Nat.le_antisymm forward backward)

/-- Sort only the selected root prefix and write it back to the original slice. -/
def canonicalize (roots : Slice U64) (count : Nat) : Slice U64 :=
  restorePrefix roots (sortedWords (prefixSlice roots count))

theorem canonicalize_frame (roots : Slice U64) (count : Nat) (room : count ≤ roots.length) :
    (canonicalize roots count).length = roots.length ∧
    (canonicalize roots count).val.take count = (sortedWords (prefixSlice roots count)).val ∧
    (canonicalize roots count).val.drop count = roots.val.drop count := by
  let window := sortedWords (prefixSlice roots count)
  have windowLen : window.val.length = count := by
    change (sortedWords (prefixSlice roots count)).length = count
    simp [Nat.min_eq_left room]
  have allWindow : window.val.take count = window.val := by
    rw [← windowLen, List.take_length]
  have exact : (canonicalize roots count).val = window.val ++ roots.val.drop count := by
    unfold canonicalize restorePrefix
    simp only [Slice.from_val]
    change roots.val.setSlice! 0 window.val = _
    simp only [List.setSlice!, List.take_zero, List.nil_append, Nat.sub_zero, Nat.zero_add,
      windowLen, Nat.min_eq_left room, allWindow]
  refine ⟨restore_length _ _, ?_, ?_⟩
  · rw [exact, List.take_append_of_le_length (by rw [windowLen]), allWindow]
  · rw [exact, ← windowLen]
    simp

theorem usizeToU8_normal (word : Usize) (bounded : word.val ≤ UScalar.max .U8) :
    ∃ value : U8, usizeToU8 word = .ok (.Ok value) ∧ value.val = word.val :=
  checked_unsigned_conversion_normal word bounded

/-- The exact order dictionary used by the retained native call observes unsigned words. -/
theorem native_order_lt (left right : U64) : core.cmp.OrdU64.partialOrdInst.lt left right =
    .ok (decide (left.val < right.val)) := rfl

end BulksketchBridge.DegreeProbeRuntime
