import BulksketchBridge.AffineSolveMapColumns
import BulksketchBridge.AffineLinearEvalSpec
import BulksketchBridge.Algebra.Trace

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Algebra.Gf64 FrobeniusTables MutableZip
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

private theorem slice_width (columns : Columns) : columns.to_slice.length = 64 :=
  Array.length_to_slice columns

private theorem slice_entry (columns : Columns) (i : Nat) :
    columns.to_slice[i]! = entry columns i := by
  simp only [Slice.getElem!_Nat_eq, Array.to_slice, Slice.from_val, entry]

theorem update_column_field (columns row : Columns) (coefficient : U64) (i : Nat) (active : i < 64) :
    toField (entry (updateColumns columns row coefficient) i).bv =
      toField (entry columns i).bv + toField coefficient.bv * toField (entry row i).bv := by
  by_cases zero : coefficient = 0#u64
  · subst coefficient
    rw [updateColumns, ite_eq_left rfl, show toField (0#u64).bv = 0 from toField_zero, zero_mul, add_zero]
  · let mapped := mapFrom columns.to_slice row.to_slice (columnTransform coefficient) 0
    have mappedWidth : mapped.val.length = (64#usize).val := by
      change mapped.length = 64
      rw [show mapped = mapFrom columns.to_slice row.to_slice (columnTransform coefficient) 0 from rfl,
        mapFrom_length, slice_width]
    have updated : entry (updateColumns columns row coefficient) i = mapped[i]! := by
      rw [updateColumns, ite_eq_right zero]
      change (Array.from_slice columns mapped).val[i]! = mapped[i]!
      rw [Array.from_slice_val _ _ mappedWidth, Slice.getElem!_Nat_eq]
    rw [updated]
    have activeColumns : i < columns.to_slice.length := by rwa [slice_width]
    have entryEq : mapped[i]! = columnTransform coefficient (entry columns i) (entry row i) := by
      unfold mapped
      rw [mapFrom_word _ _ _ _ _ activeColumns, ite_eq_left (Nat.zero_le _), slice_entry, slice_entry]
    rw [entryEq, columnTransform]
    by_cases one : coefficient = 1#u64
    · rw [ite_eq_left one, one]
      change toField ((entry columns i).bv ^^^ (entry row i).bv) =
        toField (entry columns i).bv + toField (1#u64).bv * toField (entry row i).bv
      rw [toField_xor, show toField (1#u64).bv = 1 from toField_one, one_mul]
    · rw [ite_eq_right one]
      change toField ((entry columns i).bv ^^^ multiplyWord coefficient.bv (entry row i).bv) = _
      rw [toField_xor, toField_mul]

theorem fold_column_field (linear : Slice U64) (table : Rows) (good : TablePrefix table 64)
    (start count : Nat) (columns : Columns) (bit : Nat) (bitBound : bit < 64)
    (powerRoom : start + count ≤ 64) :
    toField (entry (foldColumns linear table start columns count) bit).bv =
      toField (entry columns bit).bv +
        ∑ offset ∈ Finset.range count,
          toField linear[start + offset]!.bv * toField (column 0 bit).bv ^ (2 ^ (start + offset)) := by
  induction count generalizing start columns with
  | zero => simp only [foldColumns, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ count ih =>
    have before : start < 64 := by omega
    have row := good start before bit bitBound
    have power : toField (entry (entry table start) bit).bv = toField (column 0 bit).bv ^ (2 ^ start) := by
      rw [row]
      exact toField_iterateSquare start ((1 : BitVec 64) <<< bit)
    rw [foldColumns, ih (start + 1) (updateColumns columns (entry table start) linear[start]!) (by omega),
      update_column_field _ _ _ _ bitBound, power, Finset.sum_range_succ', Nat.add_zero]
    have offsets :
        (∑ i ∈ Finset.range count, toField linear[start + 1 + i]!.bv *
          toField (column 0 bit).bv ^ (2 ^ (start + 1 + i))) =
        ∑ i ∈ Finset.range count, toField linear[start + (i + 1)]!.bv *
          toField (column 0 bit).bv ^ (2 ^ (start + (i + 1))) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [show start + 1 + i = start + (i + 1) by omega]
    rw [offsets]
    simp only [Nat.add_zero]
    ac_rfl

/-- The exact original column fold produces the linearized polynomial
evaluated on every one of the 64 binary basis words. -/
theorem native_columns_linearized (linear : Slice U64) (table : Rows) (good : TablePrefix table 64)
    (small : linear.length ≤ 64) (bit : Nat) (bitBound : bit < 64) :
    toField (entry (foldColumns linear table 0 (Array.repeat 64#usize 0#u64) linear.length) bit).bv =
      AffineLinearEval.linearValueFrom linear (column 0 bit) 0 := by
  rw [fold_column_field _ _ good _ _ _ _ bitBound (by simpa only [Nat.zero_add] using small)]
  rw [entry_repeat _ _ _ bitBound, show toField (0#u64).bv = 0 from toField_zero, zero_add]
  simp only [AffineLinearEval.linearValueFrom, Nat.sub_zero, Nat.zero_add]


end BulksketchBridge.AffineSolveMap
