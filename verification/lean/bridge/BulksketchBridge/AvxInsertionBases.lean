import BulksketchBridge.AvxInsertionBasesInner
import BulksketchBridge.Algebra.Word

namespace BulksketchBridge.AvxInsertionBases

open Aeneas Aeneas.Std ControlFlow
open ClosedLeafAdvance (usizeWord word_val)
open Algebra.Gf64
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2300000

def route (bit : Usize) : Usize × Usize × Usize :=
  if bit.val < 54 then (usizeWord (bit.val / 6), usizeWord (bit.val % 6), 64#usize)
  else (usizeWord ((bit.val - 54) / 5), usizeWord ((bit.val - 54) % 5), 32#usize)

private theorem route_normal (bit : Usize) (room : bit.val < 64) :
    (if bit < 54#usize then do
      let chunk ← bit / 6#usize
      let shift ← bit % 6#usize
      Result.ok (chunk, shift, 64#usize)
    else do
      let rest ← bit - 54#usize
      let chunk ← rest / 5#usize
      let shift ← rest % 5#usize
      Result.ok (chunk, shift, 32#usize)) = .ok (route bit) := by
  by_cases first : bit.val < 54
  · have guard : bit < 54#usize := first
    obtain ⟨chunk, div, chunkVal⟩ := RawMulTable.normal_of_spec _ _ (Usize.div_spec bit (y := 6#usize) (by simp))
    obtain ⟨shift, rem, shiftVal⟩ := RawMulTable.normal_of_spec _ _ (Usize.rem_spec bit (y := 6#usize) (by simp))
    change chunk.val = bit.val / 6 at chunkVal
    change shift.val = bit.val % 6 at shiftVal
    have chunkEq : chunk = usizeWord (bit.val / 6) :=
      UScalar.eq_of_val_eq (chunkVal.trans (word_val _ (by have := small_usize; omega)).symm)
    have shiftEq : shift = usizeWord (bit.val % 6) :=
      UScalar.eq_of_val_eq (shiftVal.trans (word_val _ (by have := small_usize; omega)).symm)
    simp only [guard, ite_true, Bind.bind, div, rem, bind_ok, chunkEq, shiftEq, route, first]
  · have guard : ¬bit < 54#usize := first
    obtain ⟨rest, sub, restVal, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := bit) (y := 54#usize) (by change 54 ≤ bit.val; omega))
    obtain ⟨chunk, div, chunkVal⟩ := RawMulTable.normal_of_spec _ _ (Usize.div_spec rest (y := 5#usize) (by simp))
    obtain ⟨shift, rem, shiftVal⟩ := RawMulTable.normal_of_spec _ _ (Usize.rem_spec rest (y := 5#usize) (by simp))
    change rest.val = bit.val - 54 at restVal
    change chunk.val = rest.val / 5 at chunkVal
    change shift.val = rest.val % 5 at shiftVal
    rw [restVal] at chunkVal shiftVal
    have chunkEq : chunk = usizeWord ((bit.val - 54) / 5) :=
      UScalar.eq_of_val_eq (chunkVal.trans (word_val _ (by have := small_usize; omega)).symm)
    have shiftEq : shift = usizeWord ((bit.val - 54) % 5) :=
      UScalar.eq_of_val_eq (shiftVal.trans (word_val _ (by have := small_usize; omega)).symm)
    simp only [guard, ite_false, Bind.bind, sub, div, rem, bind_ok, chunkEq, shiftEq, route, first]

theorem route_bounds (bit power : Usize) (bitRoom : bit.val < 64) (powerRoom : power.val < 7) :
    ValueBounds bit power (route bit).1 (route bit).2.1 (route bit).2.2 := by
  unfold route ValueBounds
  by_cases first : bit.val < 54
  · rw [ite_eq_left first]
    have chunk : (usizeWord (bit.val / 6)).val = bit.val / 6 := word_val _ (by have := small_usize; omega)
    have shift : (usizeWord (bit.val % 6)).val = bit.val % 6 := word_val _ (by have := small_usize; omega)
    simp only [chunk, shift, show (64#usize).val = 64 by simp, first, true_implies, and_true]
    omega
  · rw [ite_eq_right first]
    have chunk : (usizeWord ((bit.val - 54) / 5)).val = (bit.val - 54) / 5 := word_val _ (by have := small_usize; omega)
    have shift : (usizeWord ((bit.val - 54) % 5)).val = (bit.val - 54) % 5 := word_val _ (by have := small_usize; omega)
    simp only [chunk, shift, show (32#usize).val = 32 by simp, first, false_implies, true_and, and_true]
    omega

theorem route_count (bit : Usize) : (route bit).2.2.val = 64 ∨ (route bit).2.2.val = 32 := by
  unfold route
  split
  · left; simp
  · right; simp

def squareColumn (column : U64) : U64 := ⟨BulksketchProofs.Field.Period.squareWord column.bv⟩

theorem square_column_normal (column : U64) :
    bulksketch.field.frobenius.square column = .ok (squareColumn column) :=
  FrobeniusConst.square_refines column

theorem square_column_field (column : U64) :
    toField (squareColumn column).bv = toField column.bv ^ 2 := toField_square column.bv

def powerStep (tables : Tables) (bit power : Usize) (column : U64) : Tables :=
  let limits := route bit
  valueFold bit (squareColumn column) power limits.1 limits.2.1 tables 1#usize (limits.2.2.val - 1)

def powerFold (bit : Usize) (tables : Tables) (column : U64) (power : Usize) : Nat → Tables
  | 0 => tables
  | count + 1 => powerFold bit (powerStep tables bit power column) (squareColumn column) (advance power) count

private theorem power_step_normal (bit power : Usize) (tables : Tables) (column : U64)
    (bitRoom : bit.val < 64) (active : power.val < 7) :
    insertion_bases_loop0_loop0.body bit tables.1 tables.2 column power =
      .ok (.cont ((powerStep tables bit power column).1, (powerStep tables bit power column).2,
        squareColumn column, advance power)) := by
  let limits := route bit
  have guard : power < 7#usize := active
  have selected := route_normal bit bitRoom
  have count := route_count bit
  have row := value_loop_refines tables bit (squareColumn column) power limits.1 limits.2.1 limits.2.2
    1#usize (limits.2.2.val - 1) (route_bounds bit power bitRoom active)
    (by change 1 + ((route bit).2.2.val - 1) = (route bit).2.2.val; omega)
  have plus := (advance_normal power (by have := small_usize; omega)).1
  simp only [insertion_bases_loop0_loop0.body, guard, ite_true, square_column_normal, bind_ok]
  simp only [Bind.bind] at selected
  with_unfolding_all rw [selected, bind_ok]
  dsimp! only
  with_unfolding_all rw [row, bind_ok]
  dsimp! only
  simp only [plus, bind_ok, powerStep, limits]

theorem power_loop_refines (bit power : Usize) (tables : Tables) (column : U64)
    (remaining : Nat) (bitRoom : bit.val < 64) (cursor : power.val + remaining = 7) :
    insertion_bases_loop0_loop0 tables.1 tables.2 bit column power =
      .ok (powerFold bit tables column power remaining) := by
  induction remaining generalizing power tables column with
  | zero =>
    have done : ¬power < 7#usize := by change ¬power.val < 7; omega
    conv_lhs => unfold insertion_bases_loop0_loop0 loop
    dsimp only
    simp only [insertion_bases_loop0_loop0.body, done, ite_false, bind_ok, powerFold]
  | succ remaining ih =>
    have step := power_step_normal bit power tables column bitRoom (by omega)
    have advanced := (advance_normal power (by have := small_usize; omega)).2
    conv_lhs => unfold insertion_bases_loop0_loop0 loop
    dsimp only
    rw [step, bind_ok]
    exact ih (advance power) (powerStep tables bit power column) (squareColumn column) (by omega)

def bitColumn (bit : Usize) : U64 := ⟨(1 : BitVec 64) <<< bit.val⟩

private theorem bit_column_normal (bit : Usize) (room : bit.val < 64) :
    (1#u64 <<< bit : Result U64) = .ok (bitColumn bit) := by
  obtain ⟨word, normal, _, bits⟩ := RawMulTable.normal_of_spec _ _
    (UScalar.ShiftLeft_spec (1#u64) bit _ room rfl)
  have wordEq : word = bitColumn bit := U64.bv_eq_imp_eq _ _ bits
  exact wordEq ▸ normal

def bitStep (tables : Tables) (bit : Usize) : Tables :=
  powerFold bit tables (bitColumn bit) 0#usize 7

def bitFold (tables : Tables) (bit : Usize) : Nat → Tables
  | 0 => tables
  | count + 1 => bitFold (bitStep tables bit) (advance bit) count

private theorem bit_step_normal (tables : Tables) (bit : Usize) (active : bit.val < 64) :
    insertion_bases_loop0.body tables.1 tables.2 bit =
      .ok (.cont ((bitStep tables bit).1, (bitStep tables bit).2, advance bit)) := by
  have guard : bit < 64#usize := active
  have column := bit_column_normal bit active
  have ran := power_loop_refines bit 0#usize tables (bitColumn bit) 7 active (by simp)
  have plus := (advance_normal bit (by have := small_usize; omega)).1
  simp only [insertion_bases_loop0.body, guard, ite_true, column, bind_ok, ran]
  dsimp! only
  simp only [plus, bind_ok, bitStep]
  rfl

theorem bit_loop_refines (tables : Tables) (bit : Usize) (remaining : Nat)
    (cursor : bit.val + remaining = 64) :
    insertion_bases_loop0 tables.1 tables.2 bit = .ok (bitFold tables bit remaining) := by
  induction remaining generalizing tables bit with
  | zero =>
    have done : ¬bit < 64#usize := by change ¬bit.val < 64; omega
    conv_lhs => unfold insertion_bases_loop0 loop
    dsimp only
    simp only [insertion_bases_loop0.body, done, ite_false, bind_ok, bitFold]
  | succ remaining ih =>
    have step := bit_step_normal tables bit (by omega)
    have advanced := (advance_normal bit (by have := small_usize; omega)).2
    conv_lhs => unfold insertion_bases_loop0 loop
    dsimp only
    rw [step, bind_ok]
    exact ih (bitStep tables bit) (advance bit) (by omega)

def zeroTables : Tables :=
  (Array.repeat 9#usize (Array.repeat 64#usize (Array.repeat 8#usize 0#u64)),
    Array.repeat 2#usize (Array.repeat 32#usize (Array.repeat 8#usize 0#u64)))

def generatedTable : InsertionBases :=
  let values := bitFold zeroTables 0#usize 64
  ⟨values.1, values.2⟩

def ActualInsertionBases : Prop :=
  insertion_bases = Result.ok generatedTable

theorem insertion_bases_refines : ActualInsertionBases := by
  unfold ActualInsertionBases insertion_bases
  have run := bit_loop_refines zeroTables 0#usize 64 (by simp)
  change (do let (six, five) ← insertion_bases_loop0 zeroTables.1 zeroTables.2 0#usize
             Result.ok ({ six, five } : InsertionBases)) = _
  simp only [Bind.bind, run, bind_ok, generatedTable]

end BulksketchBridge.AvxInsertionBases
