import BulksketchBridge.NewtonGuardSpec
import BulksketchBridge.ClosedLeafWindows
import BulksketchBridge.ReconstructionLoop
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.NewtonGuard

open Aeneas Aeneas.Std Aeneas.Std.WP DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.deg34
open NewtonGuardResidual (CorrectArithmetic)

set_option maxRecDepth 2048
set_option maxHeartbeats 1500000

@[simp] theorem clearedFrame_length (scratch : Slice U64) (words : Array U64 5#usize × U64) :
    (clearedFrame scratch words).length = scratch.length := by
  simp [clearedFrame]

private theorem restore_array_prefix (scratch : Slice U64) (words : Array U64 5#usize) :
    restorePrefix scratch words.to_slice = scratch.setSlice! 0 words.val := by
  apply Slice.ext
  simp only [restorePrefix, Slice.from_val, Array.val_to_slice, Slice.setSlice!_val]

theorem clearedFrame_prefix (scratch : Slice U64) (words : Array U64 5#usize × U64)
    (room : 6 ≤ scratch.length) (index : Nat) (bound : index < 5) :
    (clearedFrame scratch words)[index]! = words.1[index]! := by
  rw [Slice.getElem!_Nat_eq, clearedFrame, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega),
    restore_array_prefix, ← Slice.getElem!_Nat_eq]
  rw [Slice.setSlice!_getElem!_middle scratch words.1.val 0 index]
  · simp [Array.getElem!_Nat_eq]
  · simp only [Array.property, Nat.zero_le, Nat.sub_zero, true_and]
    exact ⟨bound, by omega⟩

theorem clearedFrame_denominator (scratch : Slice U64) (words : Array U64 5#usize × U64)
    (room : 6 ≤ scratch.length) : (clearedFrame scratch words)[5]! = words.2 := by
  rw [Slice.getElem!_Nat_eq, clearedFrame]
  apply Slice.getElem!_Nat_setAtNat_eq
  rw [restore_length]
  omega

theorem clearedFrame_suffix (scratch : Slice U64) (words : Array U64 5#usize × U64)
    (index : Nat) (after : 6 ≤ index) : (clearedFrame scratch words)[index]! = scratch[index]! := by
  rw [Slice.getElem!_Nat_eq, clearedFrame, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (by omega),
    restore_array_prefix, ← Slice.getElem!_Nat_eq]
  apply Slice.setSlice!_getElem!_suffix
  simp only [Array.property, Nat.zero_add]
  change 5 ≤ index
  omega

private theorem read_normal (words : Slice U64) (index : Usize)
    (bound : index.val < words.length) : Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨value, normal, post⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bound)
  rw [normal, post]
  exact congrArg Result.ok (Slice.Inhabited_getElem_eq_getElem! words index.val bound)

private theorem copy_normal (scratch : Slice U64) (words : Array U64 5#usize)
    (room : 6 ≤ scratch.length) :
    core.slice.Slice.copy_from_slice core.marker.CopyU64 (prefixSlice scratch 5) words.to_slice =
      Result.ok words.to_slice := by
  apply ClosedLeaf.copy_normal
  rw [prefix_length, Nat.min_eq_left (by omega), Array.length_to_slice]
  rfl

private theorem update_cleared (scratch : Slice U64) (five : Array U64 5#usize) (denominator : U64)
    (room : 6 ≤ scratch.length) :
    Slice.update (restorePrefix scratch five.to_slice) 5#usize denominator =
      Result.ok (clearedFrame scratch (five, denominator)) := by
  have bounded : (5#usize).val < (restorePrefix scratch five.to_slice).length := by
    rw [restore_length]
    change 5 < scratch.length
    omega
  exact Reconstruction.update_normal _ _ _ bounded

/-- The exact mutable frame is established before either original residual loop. -/
def prepared {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (odd : Slice U64) (degree : Usize) (scratch : Slice U64) : Result (Bool × Slice U64) := do
  let words := clearedWords odd degree.val
  if words.2 = 0#u64 then .ok (false, scratch) else
    let updated := clearedFrame scratch words
    let limit ← degree + 2#usize
    let range := (⟨degree, core.cmp.impls.OrdUsize.min (Slice.len odd) limit⟩ : core.ops.range.Range Usize)
    let ok ← if degree = 3#usize then guard_loop0 fieldDictionary kernels range odd degree updated words.2
             else guard_loop1 fieldDictionary kernels range odd degree updated words.2
    .ok (ok, updated)

theorem guard_preparation_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (odd : Slice U64) (degree : Usize) (scratch : Slice U64)
    (arithmetic : CorrectArithmetic kernels) (admitted : Admitted odd degree scratch) :
    bulksketch.decode.deg34.guard fieldDictionary kernels odd degree scratch = prepared kernels odd degree scratch := by
  have degreeValues : degree.val = 3 ∨ degree.val = 4 := by
    rcases admitted.degreeCases with three | four
    · left; rw [three]; rfl
    · right; rw [four]; rfl
  have room := admitted.inputRoom
  have read0 := read_normal odd 0#usize (by change 0 < odd.length; omega)
  have read1 := read_normal odd 1#usize (by change 1 < odd.length; omega)
  have read2 := read_normal odd 2#usize (by change 2 < odd.length; omega)
  change _ = Result.ok odd[0]! at read0
  change _ = Result.ok odd[1]! at read1
  change _ = Result.ok odd[2]! at read2
  have mulNormal (a b : U64) : kernels.ArithmeticInst.mul a b = .ok (mulWord a b) :=
    (arithmetic.1 a b).trans (Algebra.Gf64.native_mul_word a b)
  have squareNormal (a : U64) : kernels.ArithmeticInst.square a = .ok (squareWord a) :=
    (arithmetic.2 a).trans (Square.square_refines a)
  let words := clearedWords odd degree.val
  by_cases zero : words.2 = 0#u64
  · rcases admitted.degreeCases with three | four
    · have val : degree.val = 3 := by rw [three]; rfl
      simp only [words, clearedWords, val, eq_self, ite_true] at zero
      simp only [bulksketch.decode.deg34.guard, prepared, read0, read1, read2, squareNormal, mulNormal, bind_ok, lift,
        three, eq_self, ite_true, clearedWords, show (3#usize).val = 3 from rfl, zero]
    · have val : degree.val = 4 := by rw [four]; rfl
      have notThree : degree ≠ 3#usize := by rw [four]; decide
      have read3 := read_normal odd 3#usize (by change 3 < odd.length; omega)
      change _ = Result.ok odd[3]! at read3
      simp only [words, clearedWords, val, show (4 : Nat) ≠ 3 by decide, ite_false] at zero
      simp only [bulksketch.decode.deg34.guard, prepared, read0, read1, read2, read3, squareNormal, mulNormal, bind_ok, lift,
        notThree, ite_false, clearedWords, val, show (4 : Nat) ≠ 3 by decide, zero, eq_self, ite_true]
  · have scratchRoom := admitted.scratchRoom zero
    have prefixNormal := prefix_normal scratch 5#usize (by change 5 ≤ scratch.length; omega)
    change _ = Result.ok (prefixSlice scratch 5, restorePrefix scratch) at prefixNormal
    have copied := copy_normal scratch words.1 scratchRoom
    have updated := update_cleared scratch words.1 words.2 scratchRoom
    have finish : clearedFrame scratch (words.1, words.2) = clearedFrame scratch words := rfl
    rw [finish] at updated
    rcases admitted.degreeCases with three | four
    · have val : degree.val = 3 := by rw [three]; rfl
      simp only [words, clearedWords, val, eq_self, ite_true] at zero copied updated
      simp only [bulksketch.decode.deg34.guard, prepared, read0, read1, read2, squareNormal, mulNormal, bind_ok, lift,
        three, eq_self, ite_true, clearedWords, show (3#usize).val = 3 from rfl, zero, ite_false,
        Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefixNormal]
      dsimp! only
      rw [copied, bind_ok, updated, bind_ok]
    · have val : degree.val = 4 := by rw [four]; rfl
      have notThree : degree ≠ 3#usize := by rw [four]; decide
      have read3 := read_normal odd 3#usize (by change 3 < odd.length; omega)
      change _ = Result.ok odd[3]! at read3
      simp only [words, clearedWords, val, show (4 : Nat) ≠ 3 by decide, ite_false] at zero copied updated
      simp only [bulksketch.decode.deg34.guard, prepared, read0, read1, read2, read3, squareNormal, mulNormal, bind_ok, lift,
        notThree, ite_false, clearedWords, val, show (4 : Nat) ≠ 3 by decide, zero,
        Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefixNormal]
      dsimp! only
      rw [copied, bind_ok, updated, bind_ok]

end BulksketchBridge.NewtonGuard
