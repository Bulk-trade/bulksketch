import BulksketchBridge.FrobeniusTablesEntries

namespace BulksketchBridge.FrobeniusTables

open Aeneas Aeneas.Std FrobeniusTable

private theorem schedule_length :
    Slice.len (Array.to_slice bulksketch.field.frobenius.POWERS) = 9#usize := by
  apply UScalar.eq_of_val_eq
  simp only [Slice.len_val, Array.length_to_slice]

/-- The outer loop carries columns from the preceding scheduled power and
preserves every cell of every completed map. -/
theorem fill_maps (tables : Tables) (columns : Columns) (bit index : Usize) (power : U32)
    (bounded : index.val ≤ 9) (previous : power.val = previousPower index.val)
    (columnsCorrect : ColumnsMatch columns power.val)
    (zero : ZeroCells tables) (correct : Filled tables index.val 0 0) :
    ∃ result, bulksketch.field.frobenius.tables_loop1 tables columns bit index power =
      Result.ok result ∧ Filled result 9 0 0 := by
  apply RawMulTable.normal_of_spec
  unfold bulksketch.field.frobenius.tables_loop1
  apply loop.spec_decr_nat
    (fun state : Tables × Columns × Usize × Usize × U32 => 9 - state.2.2.2.1.val)
    (fun state => state.2.2.2.1.val ≤ 9 ∧ state.2.2.2.2.val = previousPower state.2.2.2.1.val ∧
      ColumnsMatch state.2.1 state.2.2.2.2.val ∧ ZeroCells state.1 ∧
      Filled state.1 state.2.2.2.1.val 0 0)
  · intro state invariant
    rcases state with ⟨tables, columns, bit, index, power⟩
    change index.val ≤ 9 ∧ power.val = previousPower index.val ∧ ColumnsMatch columns power.val ∧
      ZeroCells tables ∧ Filled tables index.val 0 0 at invariant
    obtain ⟨bounded, previous, columnsCorrect, zero, correct⟩ := invariant
    by_cases active : index.val < 9
    · have guard : index < 9#usize := by scalar_tac
      have within : power.val ≤ powerAt index.val := by
        rw [previous]
        exact previous_power_bound index.val active
      obtain ⟨⟨advanced, bitNext, powerNext⟩, advancedNormal, powerNextValue, advancedCorrect⟩ :=
        reach_power columns bit index power active within columnsCorrect
      obtain ⟨updated, filledNormal, zeroNext, filledCorrect⟩ :=
        fill_rows tables advanced index active advancedCorrect zero correct
      obtain ⟨next, increment, nextValue⟩ := usize_succ index (by omega)
      simp only [bulksketch.field.frobenius.tables_loop1.body, lift, bind_ok, schedule_length,
        guard, ite_true, advancedNormal]
      dsimp! only
      simp only [filledNormal, bind_ok, increment]
      apply (WP.spec_ok _).mpr
      change (next.val ≤ 9 ∧ powerNext.val = previousPower next.val ∧
        ColumnsMatch advanced powerNext.val ∧ ZeroCells updated ∧ Filled updated next.val 0 0) ∧
        9 - next.val < 9 - index.val
      refine ⟨⟨by omega, ?_, ?_, zeroNext, ?_⟩, by omega⟩
      · rw [nextValue, previousPower]
        exact powerNextValue
      · rw [powerNextValue]
        exact advancedCorrect
      · intro map nibble value mapBound nibbleBound valueBound processed
        exact filledCorrect map nibble value mapBound nibbleBound valueBound (by omega)
    · have atEnd : index.val = 9 := by omega
      have guard : ¬index < 9#usize := by scalar_tac
      simp only [bulksketch.field.frobenius.tables_loop1.body, lift, bind_ok, schedule_length,
        guard, ite_false]
      apply (WP.spec_ok _).mpr
      change Filled tables 9 0 0
      simpa only [atEnd] using correct
  · exact ⟨bounded, previous, columnsCorrect, zero, correct⟩

/-- The actual source initializer returns normally and all 2,304 entries have
the specified Frobenius value at their exact map, row, and nibble coordinates. -/
theorem tables_refines : TablesRefine := by
  let blank : Tables := Array.repeat 9#usize (Array.repeat 16#usize (Array.repeat 16#usize 0#u64))
  obtain ⟨columns, bit, initialized, _, columnsCorrect⟩ := initial_columns
  have zero : ZeroCells blank := by
    intro index row indexBound rowBound
    have ib : index < (9#usize).val := by scalar_tac
    have rb : row < (16#usize).val := by scalar_tac
    have vb : 0 < (16#usize).val := by scalar_tac
    unfold tableWord blank
    rw [entry_repeat _ _ _ ib, entry_repeat _ _ _ rb, entry_repeat _ _ _ vb]
  have initial : Filled blank 0 0 0 := by
    intro map nibble value mapBound nibbleBound valueBound processed
    omega
  obtain ⟨result, normal, correct⟩ := fill_maps blank columns bit 0#usize 0#u32
    (by scalar_tac) (by rfl) columnsCorrect zero initial
  refine ⟨result, ?_, ?_⟩
  · simp only [bulksketch.field.frobenius.tables, initialized, bind_ok]
    exact normal
  · intro index indexBound row value rowBound valueBound
    have expected := correct index row value indexBound rowBound valueBound (Or.inl indexBound)
    simpa only [mapAt, cellAt, tableWord, entry, Array.getElem!_Nat_eq] using
      congrArg U64.bv expected

end BulksketchBridge.FrobeniusTables
