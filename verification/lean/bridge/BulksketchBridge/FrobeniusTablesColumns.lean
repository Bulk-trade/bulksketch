import BulksketchBridge.FrobeniusTableSpec
import BulksketchBridge.FrobeniusConst
import BulksketchBridge.FrobeniusTablesSupport

namespace BulksketchBridge.FrobeniusTables

open Aeneas Aeneas.Std BulksketchProofs.Field.Period FrobeniusTable

abbrev Columns := Array U64 64#usize

def column (power index : Nat) : U64 :=
  ⟨iterateSquare power ((1 : BitVec 64) <<< index)⟩

/-- All 64 columns represent the current power applied to their basis bit. -/
def ColumnsMatch (columns : Columns) (power : Nat) : Prop :=
  ∀ index, index < 64 → entry columns index = column power index

def InitialPrefix (columns : Columns) (count : Nat) : Prop :=
  ∀ index, index < count → entry columns index = column 0 index

theorem initial_columns :
    ∃ columns bit, bulksketch.field.frobenius.tables_loop0 (Array.repeat 64#usize 0#u64)
      0#usize = Result.ok (columns, bit) ∧ bit.val = 64 ∧ ColumnsMatch columns 0 := by
  have complete := counted_loop 64 bulksketch.field.frobenius.tables_loop0.body
    InitialPrefix (fun columns bit => (columns, bit))
  obtain ⟨columns, bit, normal, bitValue, correct⟩ := complete (by
    intro columns bit active invariant
    have guard : bit < 64#usize := by scalar_tac
    obtain ⟨basis, shifted, _, basisBits⟩ := RawMulTable.normal_of_spec _ _
      (U64.ShiftLeft_spec (1#u64) bit active)
    have basisEq : basis = column 0 bit.val := by
      apply U64.bv_eq_imp_eq
      simpa only [column, iterateSquare, U64.ofNat_bv, UScalarTy.U64_numBits_eq,
        BitVec.ofNat_eq_ofNat] using basisBits
    obtain ⟨next, increment, nextValue⟩ := usize_succ bit (by omega)
    have writeBound : bit.val < (64#usize).val := by scalar_tac
    refine ⟨columns.set bit basis, next, ?_, nextValue, ?_⟩
    · simp only [bulksketch.field.frobenius.tables_loop0.body, guard, ite_true,
        shifted, bind_ok, update_normal columns bit basis writeBound, increment]
    · intro index earlier
      by_cases same : index = bit.val
      · subst index
        rw [entry_set_same columns bit basis writeBound, basisEq]
      · rw [entry_set_other columns bit index basis (Ne.symm same)]
        exact invariant index (by omega)) (by
    intro columns bit atEnd
    have guard : ¬bit < 64#usize := by scalar_tac
    simp only [bulksketch.field.frobenius.tables_loop0.body, guard, ite_false])
    (Array.repeat 64#usize 0#u64) 0#usize (by scalar_tac) (by
      intro index earlier
      simp at earlier)
  exact ⟨columns, bit, normal, bitValue, correct⟩

/-- A single sweep has advanced the first `count` columns exactly once. -/
def SquarePrefix (power : Nat) (columns : Columns) (count : Nat) : Prop :=
  ∀ index, index < 64 →
    entry columns index = column (if index < count then power + 1 else power) index

theorem square_columns (columns : Columns) (power : Nat) (correct : ColumnsMatch columns power) :
    ∃ updated bit, bulksketch.field.frobenius.tables_loop1_loop0_loop0 columns 0#usize =
      Result.ok (updated, bit) ∧ bit.val = 64 ∧ ColumnsMatch updated (power + 1) := by
  have complete := counted_loop 64 bulksketch.field.frobenius.tables_loop1_loop0_loop0.body
    (SquarePrefix power) (fun columns bit => (columns, bit))
  obtain ⟨updated, bit, normal, bitValue, allAdvanced⟩ := complete (by
    intro columns bit active invariant
    have guard : bit < 64#usize := by scalar_tac
    have bound : bit.val < (64#usize).val := by scalar_tac
    have old : entry columns bit.val = column power bit.val := by
      simpa only [lt_irrefl, ite_false] using invariant bit.val active
    have squared : bulksketch.field.frobenius.square (entry columns bit.val) =
        Result.ok (column (power + 1) bit.val) := by
      rw [old, FrobeniusConst.square_refines (column power bit.val)]
      rfl
    obtain ⟨next, increment, nextValue⟩ := usize_succ bit (by omega)
    refine ⟨columns.set bit (column (power + 1) bit.val), next, ?_, nextValue, ?_⟩
    · simp only [bulksketch.field.frobenius.tables_loop1_loop0_loop0.body, guard, ite_true,
        read_normal columns bit bound, bind_ok, squared, update_normal _ _ _ bound, increment]
    · intro index valid
      by_cases same : index = bit.val
      · subst index
        rw [entry_set_same _ _ _ bound, ite_eq_left (by omega : bit.val < next.val)]
      · rw [entry_set_other _ _ _ _ (Ne.symm same), invariant index valid]
        have sameBranch : (index < bit.val) ↔ (index < next.val) := by omega
        simp only [sameBranch]) (by
    intro columns bit atEnd
    have guard : ¬bit < 64#usize := by scalar_tac
    simp only [bulksketch.field.frobenius.tables_loop1_loop0_loop0.body, guard, ite_false])
    columns 0#usize (by scalar_tac) (by
      intro index valid
      simpa only [show (0#usize).val = 0 by simp, Nat.not_lt_zero, ite_false] using correct index valid)
  refine ⟨updated, bit, normal, bitValue, ?_⟩
  intro index valid
  simpa only [valid, ite_true] using allAdvanced index valid

/-- The generated constant supplies the exact source schedule at every index. -/
theorem powers_value (index : Nat) (valid : index < 9) :
    (entry bulksketch.field.frobenius.POWERS index).val = powerAt index := by
  unfold entry powerAt powers
  rw [bulksketch.field.frobenius.POWERS]
  erw [Array.make_val]
  interval_cases index <;> rfl

theorem power_bound (index : Nat) (valid : index < 9) : powerAt index ≤ 31 := by
  interval_cases index <;> decide +kernel

def previousPower : Nat → Nat
  | 0 => 0
  | index + 1 => powerAt index

theorem previous_power_bound (index : Nat) (valid : index < 9) :
    previousPower index ≤ powerAt index := by
  interval_cases index <;> decide +kernel

/-- The actual power loop carries one column array forward to the requested
schedule entry, increasing its power by exactly one on every iteration. -/
theorem reach_power (columns : Columns) (bit index : Usize) (power : U32)
    (valid : index.val < 9) (bounded : power.val ≤ powerAt index.val)
    (correct : ColumnsMatch columns power.val) :
    ∃ result : Columns × Usize × U32,
      bulksketch.field.frobenius.tables_loop1_loop0 columns bit index power = Result.ok result ∧
      result.2.2.val = powerAt index.val ∧ ColumnsMatch result.1 (powerAt index.val) := by
  have readPower := read_normal bulksketch.field.frobenius.POWERS index (by scalar_tac)
  have target := powers_value index.val valid
  have upper := power_bound index.val valid
  apply RawMulTable.normal_of_spec
  unfold bulksketch.field.frobenius.tables_loop1_loop0
  apply loop.spec_decr_nat (fun state : Columns × Usize × U32 => powerAt index.val - state.2.2.val)
    (fun state => state.2.2.val ≤ powerAt index.val ∧ ColumnsMatch state.1 state.2.2.val)
  · intro state invariant
    rcases state with ⟨columns, bit, power⟩
    change power.val ≤ powerAt index.val ∧ ColumnsMatch columns power.val at invariant
    obtain ⟨bounded, correct⟩ := invariant
    by_cases active : power.val < powerAt index.val
    · have guard : power < entry bulksketch.field.frobenius.POWERS index.val :=
        (UScalar.lt_equiv _ _).mpr (by rw [target]; exact active)
      obtain ⟨updated, bitNext, swept, _, updatedCorrect⟩ := square_columns columns power.val correct
      obtain ⟨powerNext, increment, powerNextValue⟩ := u32_succ power (by omega)
      simp only [bulksketch.field.frobenius.tables_loop1_loop0.body, readPower, bind_ok,
        guard, ite_true, swept, increment]
      apply (WP.spec_ok _).mpr
      change (powerNext.val ≤ powerAt index.val ∧ ColumnsMatch updated powerNext.val) ∧
        powerAt index.val - powerNext.val < powerAt index.val - power.val
      exact ⟨⟨by omega, by rw [powerNextValue]; exact updatedCorrect⟩, by omega⟩
    · have guard : ¬power < entry bulksketch.field.frobenius.POWERS index.val := by
        rw [UScalar.lt_equiv, target]
        exact active
      have atTarget : power.val = powerAt index.val := by omega
      simp only [bulksketch.field.frobenius.tables_loop1_loop0.body, readPower, bind_ok,
        guard, ite_false]
      exact (WP.spec_ok _).mpr ⟨atTarget, atTarget ▸ correct⟩
  · exact ⟨bounded, correct⟩

end BulksketchBridge.FrobeniusTables
