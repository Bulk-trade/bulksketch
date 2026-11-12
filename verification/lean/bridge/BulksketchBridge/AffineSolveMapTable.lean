import BulksketchBridge.AffineSolveMapSquare
import BulksketchBridge.FrobeniusTablesColumns

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Result ControlFlow
open bulksketch.decode.affine
open FrobeniusTables

set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

abbrev Rows := Array Columns 64#usize

def TablePrefix (rows : Rows) (power : Nat) : Prop :=
  ∀ row, row < power → ColumnsMatch (entry rows row) row

def BasePrefix (rows : Rows) (bit : Nat) : Prop :=
  InitialPrefix (entry rows 0) bit

theorem table_init (rows : Rows) :
    ∃ initialized last, frobenius_columns_loop0 rows 0#usize = .ok (initialized, last) ∧
      last.val = 64 ∧ TablePrefix initialized 1 := by
  have complete := counted_loop 64 frobenius_columns_loop0.body BasePrefix
    (fun rows bit => (rows, bit))
  obtain ⟨updated, bit, normal, terminal, correct⟩ := complete (by
    intro rows bit active correct
    have guard : bit < 64#usize := by scalar_tac
    have bound : bit.val < (64#usize).val := by exact active
    obtain ⟨basis, shifted, _, bits⟩ := RawMulTable.normal_of_spec _ _
      (U64.ShiftLeft_spec (1#u64) bit active)
    have value : basis = column 0 bit.val := by
      apply U64.bv_eq_imp_eq
      simpa only [column, BulksketchProofs.Field.Period.iterateSquare,
        U64.ofNat_bv, UScalarTy.U64_numBits_eq, BitVec.ofNat_eq_ofNat] using bits
    obtain ⟨next, increment, nextValue⟩ := usize_succ bit (by omega)
    let row := entry rows 0
    let written := rows.set 0#usize (row.set bit basis)
    refine ⟨written, next, ?_, nextValue, ?_⟩
    · simp only [frobenius_columns_loop0.body, guard, ite_true, bind_ok,
        read_mut_normal rows 0#usize (by decide), shifted, increment]
      dsimp! only
      have setRow : Array.update (entry rows (0#usize).val) bit basis = .ok (row.set bit basis) :=
        update_normal row bit basis bound
      simp only [setRow, bind_ok, written]
    · intro index earlier
      have setZero : entry written 0 = row.set bit basis :=
        entry_set_same rows 0#usize (row.set bit basis) (by decide)
      change entry (entry written 0) index = column 0 index
      rw [setZero]
      by_cases same : index = bit.val
      · subst index
        rw [entry_set_same row bit basis bound, value]
      · rw [entry_set_other row bit index basis (Ne.symm same)]
        exact correct index (by omega)) (by
    intro rows bit terminal
    have guard : ¬ bit < 64#usize := by scalar_tac
    simp only [frobenius_columns_loop0.body, guard, ite_false])
    rows 0#usize (by decide) (by intro index impossible; change index < 0 at impossible; omega)
  exact ⟨updated, bit, normal, terminal, fun row below => by
    have zero : row = 0 := by omega
    subst row
    exact correct⟩

def WritePrefix (original : Rows) (power : Nat) (updated : Rows) (bit : Nat) : Prop :=
  (∀ row, row ≠ power → entry updated row = entry original row) ∧
    (∀ i, i < bit → entry (entry updated power) i = column power i)

theorem table_row (rows : Rows) (power : Usize)
    (positive : 0 < power.val) (below : power.val < 64)
    (before : TablePrefix rows power.val) :
    ∃ written last, frobenius_columns_loop1_loop0 rows 0#usize power = .ok (written, last) ∧
      last.val = 64 ∧ TablePrefix written (power.val + 1) := by
  have complete := counted_loop 64 (frobenius_columns_loop1_loop0.body power)
    (WritePrefix rows power.val) (fun rows bit => (rows, bit))
  obtain ⟨written, last, normal, terminal, correct⟩ := complete (by
    intro current bit active correct
    have guard : bit < 64#usize := by scalar_tac
    have bound : bit.val < (64#usize).val := by exact active
    obtain ⟨previous, subNormal, prevValue, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := power) (y := 1#usize) (by scalar_tac))
    change previous.val = power.val - 1 at prevValue
    have prevBound : previous.val < (64#usize).val := by
      change previous.val < 64
      omega
    have powerBound : power.val < (64#usize).val := below
    have old := before previous.val (by omega) bit.val active
    have earlier := correct.1 previous.val (by omega)
    let currentRow := entry current power.val
    have squared : square_column (entry (entry current previous.val) bit.val) =
        .ok (column power.val bit.val) := by
      rw [earlier, old, square_column_refines (FrobeniusTables.column previous.val bit.val)]
      have count : power.val = previous.val + 1 := by omega
      rw [count]
      rfl
    obtain ⟨next, increment, nextValue⟩ := usize_succ bit (by omega)
    let nextRow := currentRow.set bit (column power.val bit.val)
    let nextRows := current.set power nextRow
    refine ⟨nextRows, next, ?_, nextValue, ?_⟩
    · simp only [frobenius_columns_loop1_loop0.body, guard, ite_true, bind_ok, subNormal,
        read_normal current previous prevBound, read_normal _ bit bound, squared,
        read_mut_normal current power powerBound, increment]
      dsimp! only
      have updatedRow : Array.update (entry current power.val) bit (column power.val bit.val) =
          .ok nextRow := update_normal currentRow bit _ bound
      simp only [updatedRow, bind_ok, nextRows]
    · constructor
      · intro row different
        exact (entry_set_other _ _ _ _ (Ne.symm different)).trans (correct.1 row different)
      · intro i earlier
        rw [show entry nextRows power.val = nextRow from entry_set_same _ _ _ powerBound]
        by_cases same : i = bit.val
        · subst i
          exact entry_set_same _ _ _ bound
        · rw [show entry nextRow i = entry currentRow i from
            entry_set_other _ _ _ _ (Ne.symm same)]
          exact correct.2 i (by omega)) (by
    intro current bit terminal
    have guard : ¬ bit < 64#usize := by scalar_tac
    simp only [frobenius_columns_loop1_loop0.body, guard, ite_false])
    rows 0#usize (by decide) ⟨fun _ _ => rfl, fun index impossible => by change index < 0 at impossible; omega⟩
  refine ⟨written, last, normal, terminal, ?_⟩
  intro row below
  by_cases same : row = power.val
  · subst row
    exact correct.2
  · rw [correct.1 row same]
    exact before row (by omega)

theorem table_remaining (rows : Rows) (bit power : Usize)
    (start : 0 < power.val) (bound : power.val ≤ 64)
    (correct : TablePrefix rows power.val) :
    ∃ table, frobenius_columns_loop1 rows bit power = .ok table ∧ TablePrefix table 64 := by
  suffices ∀ fuel rows bit power, 0 < power.val → power.val ≤ 64 → 64 - power.val = fuel →
      TablePrefix rows power.val →
      ∃ table, frobenius_columns_loop1 rows bit power = .ok table ∧ TablePrefix table 64 by
    exact this (64 - power.val) rows bit power start bound rfl correct
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro rows bit power positive bound fuelEq correct
    by_cases active : power.val < 64
    · obtain ⟨written, nextBit, rowNormal, _, invariant⟩ := table_row rows power positive active correct
      obtain ⟨next, inc, nextValue⟩ := usize_succ power (by omega)
      have guard : power < 64#usize := by scalar_tac
      rw [← nextValue] at invariant
      obtain ⟨table, normal, final⟩ := ih _ (by omega) written nextBit next (by omega) (by omega) rfl invariant
      refine ⟨table, ?_, final⟩
      rw [frobenius_columns_loop1, loop]
      simp only [frobenius_columns_loop1.body, guard, ite_true, rowNormal, bind_ok, inc]
      dsimp! only
      simpa only [frobenius_columns_loop1, frobenius_columns_loop1.body, bind_ok] using normal
    · have terminal : power.val = 64 := by omega
      have guard : ¬ power < 64#usize := by scalar_tac
      refine ⟨rows, ?_, terminal ▸ correct⟩
      rw [frobenius_columns_loop1, loop]
      simp only [frobenius_columns_loop1.body, guard, ite_false, bind_ok]

def ActualFrobeniusColumns : Prop :=
  ∃ table, frobenius_columns = .ok table ∧ TablePrefix table 64

theorem frobenius_columns_refines : ActualFrobeniusColumns := by
  let rows : Rows := Array.repeat 64#usize (Array.repeat 64#usize 0#u64)
  obtain ⟨initialized, bit, initial, _, correct⟩ := table_init rows
  obtain ⟨table, normal, final⟩ := table_remaining initialized bit 1#usize
    (by decide) (by decide) correct
  refine ⟨table, ?_, final⟩
  rw [frobenius_columns]
  change (do
    let (updated, next) ← frobenius_columns_loop0 rows 0#usize
    frobenius_columns_loop1 updated next 1#usize) = .ok table
  rw [initial]
  exact (bind_ok (initialized, bit) (fun pair => frobenius_columns_loop1 pair.1 pair.2 1#usize)).trans normal

theorem native_table_refines :
    ∃ table, FROBENIUS_COLUMNS = .ok table ∧ TablePrefix table 64 := by
  rw [FROBENIUS_COLUMNS]
  exact frobenius_columns_refines

#print axioms frobenius_columns_refines
#print axioms native_table_refines

end BulksketchBridge.AffineSolveMap
