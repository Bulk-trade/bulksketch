import BulksketchBridge.AffineMultiplePivot
import BulksketchBridge.AffineMultipleAlgebra

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Algebra.Gf64 ClosedLeaf DenseCoefficient RebuiltLfsr BmEntry
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1900000

/-- Read a matrix row in its original ascending coefficient order. -/
def matrixRow (matrix : Slice U64) (width row : Nat) : Slice U64 :=
  region matrix (row * width) ((row + 1) * width)

theorem region_word (words : Slice U64) (start stop index : Nat)
    (fits : stop ≤ words.length) (inside : start + index < stop) :
    (region words start stop)[index]! = words[start + index]! := by
  simp only [region, Slice.getElem!_Nat_eq, Slice.from_val]
  exact List.getElem!_slice start stop index words.val ⟨fits, inside⟩

theorem matrix_row_length (matrix : Slice U64) (width row : Nat)
    (fits : (row + 1) * width ≤ matrix.length) :
    (matrixRow matrix width row).length = width := by
  rw [matrixRow, ClosedLeaf.region_length _ _ _ fits, Nat.add_mul, Nat.one_mul]
  omega

theorem matrix_row_word (matrix : Slice U64) (width row index : Nat)
    (fits : (row + 1) * width ≤ matrix.length) (inside : index < width) :
    (matrixRow matrix width row)[index]! = matrix[row * width + index]! := by
  apply region_word _ _ _ _ fits
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem tail_word (words : Slice U64) (start index : Nat) :
    (tail words start)[index]! = words[start + index]! := by
  simp only [tail, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_drop]

theorem prefix_word (words : Slice U64) (count index : Nat) (inside : index < count) :
    (prefixSlice words count)[index]! = words[index]! := by
  simp only [prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_eq_getElem?_getD,
    List.getElem?_take, inside, ite_true]

private theorem scale_window_word (dst src : Slice U64) (factor : U64) (index : Nat)
    (inside : index < dst.length) :
    toField (scaleWindow dst src factor)[index]!.bv =
      toField dst[index]!.bv + toField factor.bv * toField src[index]!.bv := by
  rw [scaleWindow, MutableZip.mapFrom_word _ _ _ _ _ inside, ite_eq_left (Nat.zero_le _)]
  change toField (dst[index]!.bv ^^^ multiplyWord factor.bv src[index]!.bv) = _
  rw [toField_xor, toField_mul]

/-- A checked window write represents a full axpy when the source row
vanishes outside the written interval. -/
private theorem scale_write_word (dst src dstWindow srcWindow : Slice U64) (factor : U64)
    (start : Nat) (index : Nat) (inside : index < dst.length)
    (dstAt : ∀ i < dstWindow.length, dstWindow[i]! = dst[start + i]!)
    (srcAt : ∀ i < dstWindow.length, srcWindow[i]! = src[start + i]!)
    (outsideZero : ∀ i < dst.length, i < start ∨ start + dstWindow.length ≤ i → src[i]! = 0#u64) :
    toField (dst.setSlice! start (scaleWindow dstWindow srcWindow factor).val)[index]!.bv =
      toField dst[index]!.bv + toField factor.bv * toField src[index]!.bv := by
  have scaledLength : (scaleWindow dstWindow srcWindow factor).val.length = dstWindow.length := by
    change (scaleWindow dstWindow srcWindow factor).length = _
    simp [scaleWindow]
  by_cases outside : index < start ∨ start + dstWindow.length ≤ index
  · have original : (dst.setSlice! start (scaleWindow dstWindow srcWindow factor).val)[index]! =
        dst[index]! := by
      simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
      apply List.getElem!_setSlice!_same
      simpa only [scaledLength] using outside
    rw [original, outsideZero index inside outside]
    change toField dst[index]!.bv = toField dst[index]!.bv + toField factor.bv * toField 0
    rw [toField_zero, mul_zero, add_zero]
  · have relative : index - start < dstWindow.length := by omega
    have absolute : start + (index - start) = index := by omega
    have written : (dst.setSlice! start (scaleWindow dstWindow srcWindow factor).val)[index]! =
        (scaleWindow dstWindow srcWindow factor)[index - start]! := by
      simp only [Slice.getElem!_Nat_eq, Slice.setSlice!_val]
      apply List.getElem!_setSlice!_middle
      rw [scaledLength]
      change start ≤ index ∧ index - start < dstWindow.length ∧ index < dst.length
      exact ⟨by omega, relative, inside⟩
    rw [written, scale_window_word _ _ _ _ relative,
      dstAt _ relative, srcAt _ relative, absolute]

theorem eliminate_row_lengths (degree column : Nat) (rows witnesses : Slice U64)
    (row : Nat) (vector witness : Slice U64) :
    (eliminateRow degree column rows witnesses row vector witness).1.length = vector.length ∧
    (eliminateRow degree column rows witnesses row vector witness).2.length = witness.length := by
  simp only [eliminateRow, Slice.setSlice!_length, restore_length, and_self]

/-- Exact original paired writes. Prefix/suffix zeros justify reading the
native restricted windows as full linear row operations. -/
theorem eliminate_row_words (degree column : Nat) (rows witnesses : Slice U64) (row : Nat)
    (vector witness : Slice U64) (active : row < degree) (columnRoom : column ≤ degree)
    (rowsRoom : degree * degree ≤ rows.length)
    (witnessesRoom : degree * (degree + 1) ≤ witnesses.length)
    (vectorWidth : vector.length = degree) (witnessWidth : witness.length = degree + 1)
    (rowZeros : ∀ i < row, (matrixRow rows degree row)[i]! = 0#u64)
    (witnessZeros : ∀ i < degree + 1, column < i →
      (matrixRow witnesses (degree + 1) row)[i]! = 0#u64) :
    (∀ i < vector.length,
      toField (eliminateRow degree column rows witnesses row vector witness).1[i]!.bv =
        toField vector[i]!.bv + toField vector[row]!.bv * toField (matrixRow rows degree row)[i]!.bv) ∧
    (∀ i < witness.length,
      toField (eliminateRow degree column rows witnesses row vector witness).2[i]!.bv =
        toField witness[i]!.bv + toField vector[row]!.bv * toField (matrixRow witnesses (degree + 1) row)[i]!.bv) := by
  have rowFits : (row + 1) * degree ≤ rows.length :=
    (Nat.mul_le_mul_right degree (Nat.succ_le_of_lt active)).trans rowsRoom
  have witFits : (row + 1) * (degree + 1) ≤ witnesses.length :=
    (Nat.mul_le_mul_right (degree + 1) (Nat.succ_le_of_lt active)).trans witnessesRoom
  have rowEnd : (row + 1) * degree = row * degree + degree := by rw [Nat.add_mul, Nat.one_mul]
  have witEnd : (row + 1) * (degree + 1) = row * (degree + 1) + (degree + 1) := by
    rw [Nat.add_mul, Nat.one_mul]
  constructor
  · intro index inside
    unfold eliminateRow
    apply scale_write_word vector (matrixRow rows degree row) (tail vector row)
      (region rows (row * degree + row) ((row + 1) * degree)) vector[row]! row index inside
    · intro i _
      exact tail_word _ _ _
    · intro i inner
      rw [tail_length, vectorWidth] at inner
      rw [region_word _ _ _ _ rowFits (by omega), matrix_row_word _ _ _ _ rowFits (by omega)]
      rw [Nat.add_assoc]
    · intro i bounded outside
      rw [tail_length, vectorWidth] at outside
      rw [vectorWidth] at bounded
      exact rowZeros i (by omega)
  · intro index inside
    unfold eliminateRow restorePrefix
    apply scale_write_word witness (matrixRow witnesses (degree + 1) row)
      (prefixSlice witness (column + 1))
      (region witnesses (row * (degree + 1)) (row * (degree + 1) + column + 1))
      vector[row]! 0 index inside
    · intro i inner
      rw [prefix_length, Nat.min_eq_left (by omega)] at inner
      rw [prefix_word _ _ _ inner, Nat.zero_add]
    · intro i inner
      rw [prefix_length, Nat.min_eq_left (by omega)] at inner
      rw [region_word _ _ _ _ (by omega) (by omega),
        Nat.zero_add, matrix_row_word _ _ _ _ witFits (by omega)]
    · intro i bounded outside
      rw [prefix_length, Nat.min_eq_left (by omega)] at outside
      exact witnessZeros i (by omega) (by omega)

end BulksketchBridge.AffineMultiple
