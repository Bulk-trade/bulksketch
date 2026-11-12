import BulksketchBridge.DenseDivRemWindows
import BulksketchBridge.DenseDivRemCursor

namespace BulksketchBridge.DenseDivRem

open Aeneas Aeneas.Std BulksketchBridge DenseDivision
open bulksketch.backend.contract
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096

def MulWordLaw {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ left right, kernels.ArithmeticInst.mul left right = .ok (Inverse.multiplyNativeWord left right)

theorem update_zero (b : Slice U64) (offset top : Nat) (raw : Slice Raw) :
    updateRaw b 0#u64 offset top raw = raw := by
  apply Slice.ext_getElem (update_raw_length _ _ _ _ _)
  intro i updated original
  rw [Slice.Inhabited_getElem_eq_getElem! _ _ updated,
    Slice.Inhabited_getElem_eq_getElem! _ _ original, update_raw_word _ _ _ _ _ _ original]
  by_cases inside : offset ≤ i ∧ i < top
  · simp [updateWord, inside]
  · simp only [updateWord, inside, ite_false]

theorem read_normal {T : Type} [Inhabited T] (words : Slice T) (index : Usize) (bound : index.val < words.length) :
    Slice.index_usize words index = .ok words[index.val]! := by
  obtain ⟨word, normal, value⟩ := RawMulTable.normal_of_spec _ _ (Slice.index_usize_spec words index bound)
  rw [normal, value, Slice.getElem!_Nat_eq, List.Inhabited_getElem_eq_getElem! _ _ bound]

theorem reduce_normal {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (reduce : DenseMul.reduceAgrees kernels) (word : Raw) :
    kernels.ArithmeticInst.reduce word = .ok (DenseMulReductionSpec.reduceWord word) := by
  obtain ⟨value, normal, meaning, _⟩ := Gf64Reduce.reduce_refines word
  have exactValue : value = DenseMulReductionSpec.reduceWord word := U64.bv_eq_imp_eq _ _ meaning
  rw [reduce, normal, exactValue]

/-- Exact quotient-index formation and the write-back to the original scratch. -/
theorem quotient_write (q : Slice U64) (degree top : Usize) (offset : Nat)
    (offsetValue : top.val = degree.val + offset) (room : offset < q.length) :
    ∃ (slot : Usize) (old : U64), (top - degree : Result Usize) = .ok slot ∧ slot.val = offset ∧
      Slice.index_mut_usize q slot = .ok (old, q.setAtNat offset) := by
  obtain ⟨slot, offsetOk, slotValue, _⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := top) (y := degree) (by omega))
  change slot.val = top.val - degree.val at slotValue
  have slotExact : slot.val = offset := by omega
  obtain ⟨⟨old, back⟩, normal, _, write⟩ := RawMulTable.normal_of_spec _ _
    (Slice.index_mut_usize_spec q slot (by omega))
  refine ⟨slot, old, offsetOk, slotExact, ?_⟩
  rw [normal, write]
  congr 2
  funext value
  change q.setAtNat slot.val value = q.setAtNat offset value
  rw [slotExact]

end BulksketchBridge.DenseDivRem
