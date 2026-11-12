import BulksketchBridge.BmTerminal
import BulksketchBridge.AffineQuartic

namespace BulksketchBridge.BmReciprocalMeaning

open Aeneas.Std BmTerminal Algebra.Gf64

/-- The coefficient at ascending index i comes from the original
connection's degree-i slot, divided by its original constant. -/
theorem normalized_word (connection : Slice U64) (degree index : Nat)
    (degreeBound : degree < connection.length) (indexBound : index ≤ degree) :
    (normalizedConnection connection degree)[index]! =
      mulWord connection[degree - index]! (inverseWord connection[0]!) := by
  let scaled := scaledPrefix connection degree (inverseWord connection[0]!)
  have length : scaled.val.length = degree + 1 := by
    simp only [scaled, scaledPrefix, Slice.from_val, List.length_map, List.length_take]
    exact Nat.min_eq_left (by change degree + 1 ≤ connection.length; omega)
  have changed : normalizedConnection connection degree =
      connection.setSlice! 0 scaled.val.reverse := by
    apply Slice.ext
    simp only [normalizedConnection, RebuiltLfsr.restorePrefix, Slice.from_val, Slice.setSlice!_val, scaled]
  rw [changed, Slice.setSlice!_getElem!_middle connection scaled.val.reverse 0 index
    (by simp only [Nat.zero_le, Nat.sub_zero, List.length_reverse, length, true_and]; omega)]
  simp only [Nat.sub_zero]
  have reverseIndex : scaled.val.reverse[index]? = scaled.val[degree - index]? := by
    rw [List.getElem?_reverse (by omega), length]
    congr 1
  rw [List.getElem!_eq_getElem?_getD, reverseIndex]
  simp only [scaled, scaledPrefix, Slice.from_val, List.getElem?_map, List.getElem?_take]
  have inside : degree - index < connection.val.length := by
    change degree - index < connection.length
    omega
  rw [List.getElem?_eq_getElem inside]
  have before : degree - index < degree + 1 := by omega
  simp [before, ← List.Inhabited_getElem_eq_getElem! _ _ inside, Slice.getElem!_Nat_eq]

/-- The exact terminal reciprocal prefix is monic when the original
connection constant is nonzero. -/
theorem normalized_leading (connection : Slice U64) (degree : Nat)
    (room : degree < connection.length) (constant : connection[0]! ≠ 0#u64) :
    toField (normalizedConnection connection degree)[degree]!.bv = 1 := by
  rw [normalized_word connection degree degree room (Nat.le_refl _), Nat.sub_self]
  change toField (Inverse.multiplyNativeWord connection[0]! (inverseWord connection[0]!)).bv = _
  calc
    _ = toField connection[0]!.bv * toField (inverseWord connection[0]!).bv := toField_mul _ _
    _ = toField connection[0]!.bv * (toField connection[0]!.bv)⁻¹ :=
      congrArg (toField connection[0]!.bv * ·) (wordFieldEquiv.apply_symm_apply _)
    _ = 1 := mul_inv_cancel₀ (AffineQuartic.nonzero_field _ constant)

end BulksketchBridge.BmReciprocalMeaning
