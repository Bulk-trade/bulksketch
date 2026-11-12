import BulksketchBridge.FrobeniusTablesColumns
import BulksketchProofs.Field.NibbleTable

namespace BulksketchBridge.FrobeniusTables

open Aeneas Aeneas.Std BulksketchProofs.Field.Period FrobeniusTable

def tableWord (tables : Tables) (index row value : Nat) : U64 :=
  entry (entry (entry tables index) row) value

def ZeroCells (tables : Tables) : Prop :=
  ∀ index row, index < 9 → row < 16 → tableWord tables index row 0 = 0#u64

/-- The original nested loop order fills maps, rows, and nonzero values in
lexicographic order. Zero cells are preserved separately. -/
def Filled (tables : Tables) (index row count : Nat) : Prop :=
  ∀ map nibble value, map < 9 → nibble < 16 → value < 16 →
    (map < index ∨ map = index ∧ (nibble < row ∨ nibble = row ∧ value < count)) →
    tableWord tables map nibble value = ⟨cell (powerAt map) nibble value⟩

def setCell (tables : Tables) (index row value : Usize) (word : U64) : Tables :=
  tables.set index ((entry tables index.val).set row
    ((entry (entry tables index.val) row.val).set value word))

theorem setCell_read (tables : Tables) (index row value : Usize) (word : U64)
    (indexBound : index.val < 9) (rowBound : row.val < 16) (valueBound : value.val < 16)
    (map nibble slot : Nat) :
    tableWord (setCell tables index row value word) map nibble slot =
      if map = index.val ∧ nibble = row.val ∧ slot = value.val then word
      else tableWord tables map nibble slot := by
  have ib : index.val < (9#usize).val := by scalar_tac
  have rb : row.val < (16#usize).val := by scalar_tac
  have vb : value.val < (16#usize).val := by scalar_tac
  unfold setCell tableWord
  by_cases sameMap : map = index.val
  · subst map
    rw [entry_set_same _ _ _ ib]
    by_cases sameRow : nibble = row.val
    · subst nibble
      rw [entry_set_same _ _ _ rb]
      by_cases sameValue : slot = value.val
      · subst slot
        simp only [entry_set_same _ _ _ vb, true_and, ite_true]
      · rw [entry_set_other _ _ _ _ (Ne.symm sameValue)]
        simp only [sameValue, and_false, ite_false]
    · rw [entry_set_other _ _ _ _ (Ne.symm sameRow)]
      simp only [sameRow, false_and, and_false, ite_false]
  · rw [entry_set_other _ _ _ _ (Ne.symm sameMap)]
    simp only [sameMap, false_and, ite_false]

theorem cell_zero (power row : Nat) : cell power row 0 = 0 := by
  simpa [cell] using iterateSquare_zero power

/-- The source recurrence removes the lowest set bit and adds its Frobenius
column. The only finite split here is over the 15 possible nonzero nibbles. -/
theorem cell_clear_low_bit (power row value : Nat) (positive : 0 < value)
    (bounded : value < 16) :
    cell power row value =
      cell power row (value &&& (value - 1)) ^^^
        (column power (4 * row + (BitVec.ofNat 4 value).ctz.toNat)).bv := by
  have clear : BitVec.ofNat 64 value = BitVec.ofNat 64 (value &&& (value - 1)) ^^^
      ((1 : BitVec 64) <<< (BitVec.ofNat 4 value).ctz.toNat) := by
    interval_cases value <;> decide +kernel
  unfold cell column
  rw [← iterateSquare_xor]
  apply congrArg (iterateSquare power)
  calc
    BitVec.ofNat 64 value <<< (4 * row) =
        (BitVec.ofNat 64 (value &&& (value - 1)) ^^^
          ((1 : BitVec 64) <<< (BitVec.ofNat 4 value).ctz.toNat)) <<< (4 * row) := by
      exact congrArg (fun word : BitVec 64 => word <<< (4 * row)) clear
    _ = _ := by
      simp only [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add, Nat.add_comm]

theorem filled_set_next (tables : Tables) (index row value : Usize) (next : Nat)
    (indexBound : index.val < 9) (rowBound : row.val < 16) (valueBound : value.val < 16)
    (nextValue : next = value.val + 1) (correct : Filled tables index.val row.val value.val) :
    Filled (setCell tables index row value ⟨cell (powerAt index.val) row.val value.val⟩)
      index.val row.val next := by
  intro map nibble slot mapBound nibbleBound slotBound processed
  rw [setCell_read _ _ _ _ _ indexBound rowBound valueBound]
  by_cases same : map = index.val ∧ nibble = row.val ∧ slot = value.val
  · obtain ⟨rfl, rfl, rfl⟩ := same
    simp
  · rw [ite_eq_right same]
    exact correct map nibble slot mapBound nibbleBound slotBound (by omega)

theorem zero_set_nonzero (tables : Tables) (index row value : Usize) (word : U64)
    (indexBound : index.val < 9) (rowBound : row.val < 16) (valueBound : value.val < 16)
    (positive : 0 < value.val) (zero : ZeroCells tables) :
    ZeroCells (setCell tables index row value word) := by
  intro map nibble mapBound nibbleBound
  rw [setCell_read _ _ _ _ _ indexBound rowBound valueBound,
    ite_eq_right (by omega : ¬(map = index.val ∧ nibble = row.val ∧ 0 = value.val))]
  exact zero map nibble mapBound nibbleBound

/-- Both mutable backward updates in the generated body preserve the frame
outside the selected cell. All reads, scalar arithmetic and casts are checked. -/
theorem value_step (tables : Tables) (columns : Columns) (index row value : Usize)
    (indexBound : index.val < 9) (rowBound : row.val < 16)
    (positive : 0 < value.val) (valueBound : value.val < 16)
    (columnsCorrect : ColumnsMatch columns (powerAt index.val))
    (correct : Filled tables index.val row.val value.val) :
    ∃ next, bulksketch.field.frobenius.tables_loop1_loop1_loop0.body columns index row tables value =
      Result.ok (.cont (setCell tables index row value ⟨cell (powerAt index.val) row.val value.val⟩, next)) ∧
      next.val = value.val + 1 := by
  have valueGuard : value < 16#usize := by scalar_tac
  have rowGuard : row < 16#usize := by scalar_tac
  obtain ⟨previous, subtract, previousValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.sub_spec (x := value) (y := 1#usize) (by scalar_tac))
  have clearedValue : (value &&& previous).val = value.val &&& (value.val - 1) := by
    simp only [UScalar.val_and, previousValue, show (1#usize).val = 1 by simp]
  have clearBounds := BulksketchProofs.Field.nibble_low_bit_bounds value.val positive valueBound
  have earlier : (value &&& previous).val < value.val := by rw [clearedValue]; exact clearBounds.1
  obtain ⟨base, multiply, baseValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.mul_spec (x := 4#usize) (y := row) (by scalar_tac))
  obtain ⟨zeroCount, trailing, countValue, countBound⟩ :=
    usize_trailing_zeros_nibble value (by omega) valueBound
  have castValue := U32.cast_Usize_val_eq zeroCount
  obtain ⟨address, add, addressValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := base) (y := UScalar.cast .Usize zeroCount) (by scalar_tac))
  have columnAddress : address.val = 4 * row.val + (BitVec.ofNat 4 value.val).ctz.toNat := by
    rw [addressValue, baseValue, castValue, countValue]
    simp
  have columnBound : address.val < 64 := by scalar_tac
  have prior := correct index.val row.val (value &&& previous).val indexBound rowBound (by omega)
    (Or.inr ⟨rfl, Or.inr ⟨rfl, earlier⟩⟩)
  have cellValue : tableWord tables index.val row.val (value &&& previous).val ^^^
      entry columns address.val = (⟨cell (powerAt index.val) row.val value.val⟩ : U64) := by
    rw [prior, columnsCorrect address.val columnBound]
    apply U64.bv_eq_imp_eq
    change cell (powerAt index.val) row.val (value &&& previous).val ^^^
      (column (powerAt index.val) address.val).bv = _
    rw [clearedValue, columnAddress]
    exact (cell_clear_low_bit _ _ _ positive valueBound).symm
  obtain ⟨next, increment, nextValue⟩ := usize_succ value (by omega)
  have readMap := read_normal tables index (by scalar_tac)
  have readRow := read_normal (entry tables index.val) row (by scalar_tac)
  have readPrior := read_normal (entry (entry tables index.val) row.val) (value &&& previous)
    (by scalar_tac)
  have readColumn := read_normal columns address (by scalar_tac)
  have mutateMap := read_mut_normal tables index (by scalar_tac)
  have mutateRow := read_mut_normal (entry tables index.val) row (by scalar_tac)
  have update := update_normal (entry (entry tables index.val) row.val) value
    (⟨cell (powerAt index.val) row.val value.val⟩ : U64) (by scalar_tac)
  unfold tableWord at cellValue
  refine ⟨next, ?_, nextValue⟩
  simp only [bulksketch.field.frobenius.tables_loop1_loop1_loop0.body, valueGuard, ite_true,
    readMap, bind_ok, massert, rowGuard, subtract, lift, readRow, readPrior, multiply,
    trailing, add, readColumn, mutateMap, cellValue, increment, setCell]
  dsimp! only
  simp only [mutateRow, bind_ok]
  dsimp! only
  simp only [update, bind_ok]

theorem fill_values (tables : Tables) (columns : Columns) (index row : Usize)
    (indexBound : index.val < 9) (rowBound : row.val < 16)
    (columnsCorrect : ColumnsMatch columns (powerAt index.val))
    (zero : ZeroCells tables) (correct : Filled tables index.val row.val 0) :
    ∃ final, bulksketch.field.frobenius.tables_loop1_loop1_loop0 tables columns index row 1#usize =
      Result.ok final ∧ ZeroCells final ∧ Filled final index.val row.val 16 := by
  have complete := counted_loop 16
    (bulksketch.field.frobenius.tables_loop1_loop1_loop0.body columns index row)
    (fun tables count => 0 < count ∧ ZeroCells tables ∧ Filled tables index.val row.val count)
    (fun tables _ => tables)
  obtain ⟨final, _, normal, _, _, zeroFinal, correctFinal⟩ := complete (by
    intro tables value active invariant
    obtain ⟨positive, zero, correct⟩ := invariant
    obtain ⟨next, normal, nextValue⟩ := value_step tables columns index row value indexBound rowBound
      positive active columnsCorrect correct
    exact ⟨_, next, normal, nextValue, by omega,
      zero_set_nonzero _ _ _ _ _ indexBound rowBound active positive zero,
      filled_set_next _ _ _ _ _ indexBound rowBound active nextValue correct⟩) (by
    intro tables value atEnd
    have guard : ¬value < 16#usize := by scalar_tac
    simp only [bulksketch.field.frobenius.tables_loop1_loop1_loop0.body, guard, ite_false])
    tables 1#usize (by scalar_tac) (by
      refine ⟨by scalar_tac, zero, ?_⟩
      intro map nibble value mapBound nibbleBound valueBound processed
      by_cases previous : map < index.val ∨ map = index.val ∧ nibble < row.val
      · exact correct map nibble value mapBound nibbleBound valueBound (by omega)
      · have one : (1#usize).val = 1 := by simp
        obtain ⟨rfl, rfl, rfl⟩ : map = index.val ∧ nibble = row.val ∧ value = 0 := by omega
        rw [zero _ _ indexBound rowBound, cell_zero]
        rfl)
  exact ⟨final, normal, zeroFinal, correctFinal⟩

theorem fill_rows (tables : Tables) (columns : Columns) (index : Usize)
    (indexBound : index.val < 9) (columnsCorrect : ColumnsMatch columns (powerAt index.val))
    (zero : ZeroCells tables) (correct : Filled tables index.val 0 0) :
    ∃ final, bulksketch.field.frobenius.tables_loop1_loop1 tables columns index 0#usize =
      Result.ok final ∧ ZeroCells final ∧ Filled final index.val 16 0 := by
  have complete := counted_loop 16 (bulksketch.field.frobenius.tables_loop1_loop1.body columns index)
    (fun tables row => ZeroCells tables ∧ Filled tables index.val row 0) (fun tables _ => tables)
  obtain ⟨final, _, normal, _, zeroFinal, correctFinal⟩ := complete (by
    intro tables row active invariant
    obtain ⟨zero, correct⟩ := invariant
    obtain ⟨updated, filled, zeroNext, correctNext⟩ :=
      fill_values tables columns index row indexBound active columnsCorrect zero correct
    obtain ⟨next, increment, nextValue⟩ := usize_succ row (by omega)
    have guard : row < 16#usize := by scalar_tac
    refine ⟨updated, next, ?_, nextValue, zeroNext, ?_⟩
    · simp only [bulksketch.field.frobenius.tables_loop1_loop1.body, guard, ite_true,
        filled, bind_ok, increment]
    · intro map nibble value mapBound nibbleBound valueBound processed
      exact correctNext map nibble value mapBound nibbleBound valueBound (by omega)) (by
    intro tables row atEnd
    have guard : ¬row < 16#usize := by scalar_tac
    simp only [bulksketch.field.frobenius.tables_loop1_loop1.body, guard, ite_false])
    tables 0#usize (by scalar_tac) (by
      exact ⟨zero, by simpa only [show (0#usize).val = 0 by simp] using correct⟩)
  exact ⟨final, normal, zeroFinal, correctFinal⟩

end BulksketchBridge.FrobeniusTables
