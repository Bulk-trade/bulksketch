import Arithmetic.AvxInsertionBasesGenerated
import BulksketchBridge.FrobeniusTablesSupport
import BulksketchBridge.FrobeniusConst
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.AvxInsertionBases

open Aeneas Aeneas.Std ControlFlow
open FrobeniusTables
open ClosedLeafAdvance (usizeWord word_val)
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

abbrev Table (chunks values : Usize) := Array (Array (Array U64 8#usize) values) chunks
abbrev Six := Table 9#usize 64#usize
abbrev Five := Table 2#usize 32#usize
abbrev Tables := Six × Five

def cell {chunks values : Usize} (table : Table chunks values) (chunk value power : Nat) : U64 :=
  entry (entry (entry table chunk) value) power

def xorCell {chunks values : Usize} (table : Table chunks values)
    (chunk value power : Usize) (column : U64) : Table chunks values :=
  let valuesAt := entry table chunk.val
  let row := entry valuesAt value.val
  table.set chunk (valuesAt.set value (row.set power (entry row power.val ^^^ column)))

theorem xor_cell_normal {α : Type} {chunks values : Usize} (table : Table chunks values)
    (chunk value power : Usize) (column : U64)
    (chunkRoom : chunk.val < chunks.val) (valueRoom : value.val < values.val) (powerRoom : power.val < 8)
    (finish : Table chunks values → α) :
    (do
      let rows ← Array.index_usize table chunk
      let row ← Array.index_usize rows value
      let previous ← Array.index_usize row power
      let word ← lift (previous ^^^ column)
      let (rows, restoreRows) ← Array.index_mut_usize table chunk
      let (row, restoreRow) ← Array.index_mut_usize rows value
      let updated ← Array.update row power word
      Result.ok (finish (restoreRows (restoreRow updated)))) =
      .ok (finish (xorCell table chunk value power column)) := by
  have bounded : power.val < (8#usize).val := by exact powerRoom
  simp only [Bind.bind, read_normal table chunk chunkRoom, bind_ok,
    read_normal (entry table chunk.val) value valueRoom,
    read_normal (entry (entry table chunk.val) value.val) power bounded, lift,
    read_mut_normal table chunk chunkRoom, read_mut_normal (entry table chunk.val) value valueRoom]
  simp only [update_normal _ power _ bounded, bind_ok, xorCell]

def advance (cursor : Usize) : Usize := usizeWord (cursor.val + 1)

theorem advance_normal (cursor : Usize) (room : cursor.val + 1 ≤ Usize.max) :
    (cursor + 1#usize : Result Usize) = .ok (advance cursor) ∧ (advance cursor).val = cursor.val + 1 := by
  obtain ⟨next, normal, exact⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := cursor) (y := 1#usize) (by exact room))
  have value : (advance cursor).val = cursor.val + 1 := word_val _ room
  have same : next = advance cursor := UScalar.eq_of_val_eq (exact.trans value.symm)
  exact ⟨same ▸ normal, value⟩

theorem small_usize : 65 ≤ Usize.max := by
  simp only [Usize.max, Usize.numBits, UScalarTy.numBits]
  rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> decide

def bitMask (shift : Usize) : Usize := ⟨(1#usize).bv <<< shift.val⟩

private theorem mask_normal (shift : Usize) (room : shift.val < 6) :
    (1#usize <<< shift : Result Usize) = .ok (bitMask shift) := by
  have bits : 6 ≤ UScalarTy.Usize.numBits := by
    change 6 ≤ System.Platform.numBits
    rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> decide
  obtain ⟨mask, normal, _, exact⟩ := RawMulTable.normal_of_spec _ _
    (UScalar.ShiftLeft_spec (1#usize) shift _ (room.trans_le bits) rfl)
  have same : mask = bitMask shift := Usize.bv_eq_imp_eq _ _ exact
  exact same ▸ normal

def valueStep (tables : Tables) (bit : Usize) (column : U64) (power chunk shift value : Usize) : Tables :=
  if value &&& bitMask shift ≠ 0#usize then
    if bit.val < 54 then (xorCell tables.1 chunk value power column, tables.2)
    else (tables.1, xorCell tables.2 chunk value power column)
  else tables

def valueFold (bit : Usize) (column : U64) (power chunk shift : Usize)
    (tables : Tables) (value : Usize) : Nat → Tables
  | 0 => tables
  | count + 1 => valueFold bit column power chunk shift
      (valueStep tables bit column power chunk shift value) (advance value) count

/-- Native chunk admission derived later from the bit quotient and remainder. -/
def ValueBounds (bit power chunk shift count : Usize) : Prop :=
  power.val < 7 ∧ shift.val < 6 ∧
  (bit.val < 54 → chunk.val < 9 ∧ count.val = 64) ∧
  (54 ≤ bit.val → chunk.val < 2 ∧ count.val = 32)

private theorem value_step_normal (tables : Tables) (bit : Usize) (column : U64)
    (power chunk shift count value : Usize) (bounded : ValueBounds bit power chunk shift count)
    (active : value.val < count.val) :
    insertion_bases_loop0_loop0_loop0.body bit column power chunk shift count tables.1 tables.2 value =
      .ok (.cont ((valueStep tables bit column power chunk shift value).1,
        (valueStep tables bit column power chunk shift value).2, advance value)) := by
  obtain ⟨powerRoom, shiftRoom, sixRoom, fiveRoom⟩ := bounded
  have countRoom : count.val ≤ 64 := by
    by_cases first : bit.val < 54
    · rw [(sixRoom first).2]
    · rw [(fiveRoom (by omega)).2]; decide
  have plus := (advance_normal value (by have := small_usize; omega)).1
  have mask := mask_normal shift shiftRoom
  have valueActive : value < count := active
  simp only [insertion_bases_loop0_loop0_loop0.body, valueActive, ite_true, mask, bind_ok, lift]
  by_cases set : value &&& bitMask shift = 0#usize
  · simp only [set, bne_self_eq_false, Bool.false_eq_true, ite_false, bind_ok, valueStep, ne_eq, eq_self, not_true_eq_false]
    dsimp! only
    simp only [plus, bind_ok]
  · have test : ((value &&& bitMask shift) != 0#usize) = true := by simp [set]
    simp only [test, ite_true]
    by_cases first : bit.val < 54
    · obtain ⟨chunkRoom, countEq⟩ := sixRoom first
      have order : bit < 54#usize := first
      have c : chunk.val < (9#usize).val := chunkRoom
      have v : value.val < (64#usize).val := by change value.val < 64; omega
      have p : power.val < (8#usize).val := by exact Nat.lt_trans powerRoom (by decide)
      simp only [order, ite_true, read_normal tables.1 chunk c,
        read_normal (entry tables.1 chunk.val) value v,
        read_normal (entry (entry tables.1 chunk.val) value.val) power p,
        read_mut_normal tables.1 chunk c,
        update_normal _ power _ p, plus, bind_ok, valueStep, set, first, ne_eq, not_false_eq_true, xorCell]
      dsimp! only
      simp only [read_mut_normal (entry tables.1 chunk.val) value v, bind_ok]
      dsimp! only
      simp only [bind_ok]
      rfl
    · obtain ⟨chunkRoom, countEq⟩ := fiveRoom (by omega)
      have order : ¬ bit < 54#usize := first
      have c : chunk.val < (2#usize).val := chunkRoom
      have v : value.val < (32#usize).val := by change value.val < 32; omega
      have p : power.val < (8#usize).val := by exact Nat.lt_trans powerRoom (by decide)
      simp only [order, ite_false, read_normal tables.2 chunk c,
        read_normal (entry tables.2 chunk.val) value v,
        read_normal (entry (entry tables.2 chunk.val) value.val) power p,
        read_mut_normal tables.2 chunk c,
        update_normal _ power _ p, plus, bind_ok, valueStep, set, first, ne_eq, not_false_eq_true, xorCell, ite_true]
      dsimp! only
      simp only [read_mut_normal (entry tables.2 chunk.val) value v, bind_ok]
      dsimp! only
      simp only [bind_ok]
      rfl

/-- Exact descending-free value loop. Every reachable source cursor advances
once, and a selected cell receives the current square column exactly once. -/
theorem value_loop_refines (tables : Tables) (bit : Usize) (column : U64)
    (power chunk shift count value : Usize) (remaining : Nat)
    (bounds : ValueBounds bit power chunk shift count)
    (cursor : value.val + remaining = count.val) :
    insertion_bases_loop0_loop0_loop0 tables.1 tables.2 bit column power chunk shift count value =
      .ok (valueFold bit column power chunk shift tables value remaining) := by
  induction remaining generalizing tables value with
  | zero =>
    have done : ¬ value < count := by change ¬value.val < count.val; omega
    conv_lhs => unfold insertion_bases_loop0_loop0_loop0 loop
    dsimp only
    simp only [insertion_bases_loop0_loop0_loop0.body, done, ite_false, bind_ok, valueFold]
  | succ remaining ih =>
    have active : value.val < count.val := by omega
    have countRoom : count.val ≤ 64 := by
      by_cases first : bit.val < 54
      · rw [(bounds.2.2.1 first).2]
      · rw [(bounds.2.2.2 (by omega)).2]; decide
    have advanced := (advance_normal value (by have := small_usize; omega)).2
    have step := value_step_normal tables bit column power chunk shift count value bounds active
    conv_lhs => unfold insertion_bases_loop0_loop0_loop0 loop
    dsimp only
    rw [step, bind_ok]
    exact ih (valueStep tables bit column power chunk shift value) (advance value) (by omega)

end BulksketchBridge.AvxInsertionBases
