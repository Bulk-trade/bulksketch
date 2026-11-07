import BulksketchBridge.FrobeniusLookupMath
import BulksketchBridge.MapsQuadraticValue
import Mathlib.Tactic.IntervalCases

namespace BulksketchBridge.FrobeniusTable

open Aeneas Aeneas.Std BulksketchProofs.Field.Period

abbrev Iterator := core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter Row)

private def indexWord (index : Nat) : Usize := ⟨BitVec.ofNat _ index⟩

private theorem pointerCapacity : 64 ≤ UScalar.max .Usize := by
  rcases System.Platform.numBits_eq with width | width <;>
    simp [UScalar.max, UScalarTy.numBits, width]

private theorem indexWord_val (index : Nat) (bound : index ≤ 64) :
    (indexWord index).val = index := by
  change index % (2 ^ System.Platform.numBits) = index
  rcases System.Platform.numBits_eq with width | width <;>
    rw [width] <;> apply Nat.mod_eq_of_lt <;> omega

def iteratorAt (table : Map) (count : Nat) : Iterator :=
  ⟨⟨Array.to_slice table, count⟩, indexWord count⟩

private theorem index_add_one (index : Nat) (bound : index < 16) :
    indexWord index + 1#usize = Result.ok (indexWord (index + 1)) := by
  have fits : (indexWord index).val + (1#usize).val ≤ UScalar.max .Usize := by
    rw [indexWord_val index (by omega), show (1#usize).val = 1 by simp]
    have := pointerCapacity
    omega
  have normal := UScalar.add_spec fits
  cases h : indexWord index + 1#usize using Result.cases with
  | ret value =>
    simp only [h, WP.spec_ok] at normal
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    simpa [indexWord_val index (by omega), indexWord_val (index + 1) (by omega)] using normal
  | vis effect continuation => simp [h] at normal
  | div => simp [h] at normal

private theorem index_multiply_four (index : Nat) (bound : index < 16) :
    4#usize * indexWord index = Result.ok (indexWord (4 * index)) := by
  have fits : (4#usize).val * (indexWord index).val ≤ UScalar.max .Usize := by
    rw [indexWord_val index (by omega), show (4#usize).val = 4 by simp]
    have := pointerCapacity
    omega
  have normal := UScalar.mul_spec fits
  cases h : 4#usize * indexWord index using Result.cases with
  | ret value =>
    simp only [h, WP.spec_ok] at normal
    apply congrArg Result.ok
    apply UScalar.eq_of_val_eq
    simpa [indexWord_val index (by omega), indexWord_val (4 * index) (by omega)] using normal
  | vis effect continuation => simp [h] at normal
  | div => simp [h] at normal

private theorem next_row (table : Map) (index : Nat) (bound : index < 16) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Row) (iteratorAt table index) =
      Result.ok (some (indexWord index, table[index]!), iteratorAt table (index + 1)) := by
  have active : index < (Array.to_slice table).len.val := by simpa using bound
  simp only [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt,
    core.slice.iter.IteratorSliceIter.next, active, bind_ok, index_add_one index bound]
  simp [getElem!_pos, Array.val_to_slice, bound]

private theorem next_terminal (table : Map) :
    core.iter.adapters.enumerate.IteratorEnumerate.next
        (core.iter.traits.iterator.IteratorSliceIter Row) (iteratorAt table 16) =
      Result.ok (none, iteratorAt table 16) := by
  simp [core.iter.adapters.enumerate.IteratorEnumerate.next, iteratorAt,
    core.slice.iter.IteratorSliceIter.next]

private theorem right_shift (word : U64) (index : Nat) (bound : index < 16) :
    word >>> indexWord (4 * index) = Result.ok (⟨word.bv >>> (4 * index)⟩ : U64) := by
  change UScalar.shiftRight word (indexWord (4 * index)).val = _
  rw [indexWord_val _ (by omega)]
  simp only [UScalar.shiftRight, UScalarTy.U64_numBits_eq, show 4 * index < 64 by omega, ite_true]
  rfl

private theorem index_read {α : Type} [Inhabited α] {n : Usize} (array : Array α n)
    (index : Usize) (bound : index.val < n.val) :
    Array.index_usize array index = Result.ok (array[index.val]!) := by
  have valid : index.val < array.val.length := by simpa using bound
  simp [Array.index_usize, Array.getElem?_Usize_eq, List.getElem?_eq_getElem valid,
    Array.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD]

private theorem entry_read (table : Map) (power : Nat) (tableCorrect : Matches power table)
    (word : U64) (row : Nat) (bound : row < 16) :
    Array.index_usize table[row]! (UScalar.cast .Usize (RawMulAccum.nibbleWord word row)) =
      Result.ok (⟨cell power row (nibble word.bv row).toNat⟩ : U64) := by
  have bounds := RawMulAccum.nibble_bounds word row bound
  have exactIndex := congrArg (fun bits : BitVec 4 => bits.toNat) bounds.2.2.2.2
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt bounds.2.2.1] at exactIndex
  rw [index_read _ _ (by simpa using bounds.2.2.1)]
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  rw [show (UScalar.cast .Usize (RawMulAccum.nibbleWord word row)).val =
    (nibble word.bv row).toNat from exactIndex]
  exact tableCorrect row _ bound (BitVec.isLt _)

private theorem lookup_step (table : Map) (power : Nat) (tableCorrect : Matches power table)
    (word : U64) (count : Nat) (bound : count < 16) :
    bulksketch.field.frobenius.lookup_loop0.body word (iteratorAt table count)
      (⟨lookupPrefix power word.bv count⟩ : U64) =
      Result.ok (ControlFlow.cont (iteratorAt table (count + 1),
        (⟨lookupPrefix power word.bv (count + 1)⟩ : U64))) := by
  rw [bulksketch.field.frobenius.lookup_loop0.body, next_row table count bound]
  simp only [bind_ok]
  change (do
    let shift ← 4#usize * indexWord count
    let shifted ← word >>> shift
    let masked ← lift (shifted &&& 15#u64)
    let entryIndex ← Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from masked
    let index ← core.result.Result.expect
      bulksketch.core.num.error.TryFromIntError.Insts.CoreFmtDebug entryIndex (toStr "nibble index")
    let entry ← Array.index_usize table[count]! index
    let accumulated ← lift ((⟨lookupPrefix power word.bv count⟩ : U64) ^^^ entry)
    Result.ok (ControlFlow.cont (iteratorAt table (count + 1), accumulated))) = _
  simp only [index_multiply_four count bound, right_shift word count bound, Bind.bind, bind_ok,
    lift, MapsQuadratic.masked_conversion_normal, core.result.Result.expect]
  change (do
    let entry ← Array.index_usize table[count]!
      (UScalar.cast .Usize (RawMulAccum.nibbleWord word count))
    Result.ok (ControlFlow.cont (iteratorAt table (count + 1),
      (⟨lookupPrefix power word.bv count⟩ : U64) ^^^ entry))) = _
  rw [entry_read table power tableCorrect word count bound]
  simp only [Bind.bind, bind_ok, prefix_step power word.bv count]
  rfl

/-- Every remaining source loop step finishes with the complete Frobenius image. -/
theorem lookup_loop_refines (table : Map) (power : Nat) (tableCorrect : Matches power table)
    (word : U64) (count : Nat) (bound : count ≤ 16) :
    bulksketch.field.frobenius.lookup_loop0 (iteratorAt table count) word
      (⟨lookupPrefix power word.bv count⟩ : U64) =
      Result.ok (⟨iterateSquare power word.bv⟩ : U64) := by
  suffices ∀ remaining count, count ≤ 16 → 16 - count = remaining →
    bulksketch.field.frobenius.lookup_loop0 (iteratorAt table count) word
      (⟨lookupPrefix power word.bv count⟩ : U64) =
        Result.ok (⟨iterateSquare power word.bv⟩ : U64) from
    this (16 - count) count bound rfl
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro count bounded remainingEq
    by_cases done : count = 16
    · subst count
      unfold bulksketch.field.frobenius.lookup_loop0 loop
      dsimp only
      have terminal : bulksketch.field.frobenius.lookup_loop0.body word (iteratorAt table 16)
          (⟨lookupPrefix power word.bv 16⟩ : U64) =
            Result.ok (ControlFlow.done (⟨iterateSquare power word.bv⟩ : U64)) := by
        rw [bulksketch.field.frobenius.lookup_loop0.body, next_terminal]
        simp only [bind_ok, prefix_complete]
        rfl
      rw [terminal]
      simp only [bind_ok]
    · have active : count < 16 := by omega
      have recursive := ih (16 - (count + 1)) (by omega) (count + 1) (by omega) rfl
      unfold bulksketch.field.frobenius.lookup_loop0 loop
      dsimp only
      rw [lookup_step table power tableCorrect word count active]
      simp only [bind_ok]
      exact recursive

private theorem start_scan (table : Map) (power : Nat) (tableCorrect : Matches power table)
    (word : U64) :
    (do
      let iterator ← core.slice.Slice.iter (Array.to_slice table)
      let enumerated ← core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Row) iterator
      bulksketch.field.frobenius.lookup_loop0 enumerated word 0#u64) =
        Result.ok (⟨iterateSquare power word.bv⟩ : U64) := by
  have complete := lookup_loop_refines table power tableCorrect word 0 (by decide)
  have zeroIndex : indexWord 0 = 0#usize := by
    apply UScalar.eq_of_val_eq
    simp [indexWord_val]
  have zeroWord : (⟨(0 : BitVec 64)⟩ : U64) = 0#u64 := by
    apply U64.bv_eq_imp_eq
    simp
  simpa only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, Bind.bind, bind_ok, iteratorAt,
    zeroIndex, prefix_zero, zeroWord] using complete

private theorem lookup_branch (tables : Tables) (normal : bulksketch.field.frobenius.TABLES = .ok tables)
    (index : Usize) (bound : index.val < 9) (power : Nat)
    (tableCorrect : Matches power (mapAt tables index.val)) (word : U64) :
    (do
      let allTables ← bulksketch.field.frobenius.TABLES
      let table ← Array.index_usize allTables index
      let slice ← lift (Array.to_slice table)
      let iterator ← core.slice.Slice.iter slice
      let enumerated ← core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Row) iterator
      let result ← bulksketch.field.frobenius.lookup_loop0 enumerated word 0#u64
      Result.ok (some result)) =
        Result.ok (some (⟨iterateSquare power word.bv⟩ : U64)) := by
  rw [normal]
  simp only [bind_ok, index_read tables index (by simpa using bound), lift,
    core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default]
  have scan := start_scan (mapAt tables index.val) power tableCorrect word
  simp only [core.slice.Slice.iter, core.iter.traits.iterator.Iterator.enumerate.trait_default,
    core.iter.traits.iterator.Iterator.enumerate.default, bind_ok, mapAt] at scan
  rw [scan]
  simp only [bind_ok]

private theorem low_index (power : U32) (lo : 1 ≤ power.val) (hi : power.val ≤ 7) :
    ∃ difference : U32, power - 1#u32 = Result.ok difference ∧
      Usize.Insts.CoreConvertTryFromU32TryFromIntError.try_from difference =
        .ok (.Ok (indexWord (power.val - 1))) := by
  have normal := UScalar.sub_spec (x := power) (y := 1#u32) (by simpa using lo)
  cases resultEq : power - 1#u32 using Result.cases with
  | ret difference =>
    simp only [resultEq, WP.spec_ok] at normal
    have differenceVal : difference.val = power.val - 1 := by simpa using normal.1
    obtain ⟨index, conversion, value⟩ := checked_unsigned_conversion_normal
      (target := .Usize) difference (by rw [differenceVal]; have := pointerCapacity; omega)
    refine ⟨difference, rfl, ?_⟩
    have same : index = indexWord (power.val - 1) := by
      apply UScalar.eq_of_val_eq
      rw [value, differenceVal, indexWord_val _ (by omega)]
    exact same ▸ conversion
  | vis effect continuation => simp [resultEq] at normal
  | div => simp [resultEq] at normal

/-- The original selector and all five generated branches refine the fixed schedule. -/
theorem lookup_of_tables (correct : TablesRefine) (word : U64) (power : U32) :
    bulksketch.field.frobenius.lookup word power =
      Result.ok (if power.val ∈ powers then some (⟨iterateSquare power.val word.bv⟩ : U64)
        else none) := by
  obtain ⟨tables, init, entries⟩ := correct
  have normal : bulksketch.field.frobenius.TABLES = .ok tables := by
    rw [bulksketch.field.frobenius.TABLES, init]
  by_cases lo : 1 ≤ power.val
  · have low : 1#u32 ≤ power := by exact lo
    by_cases hi : power.val ≤ 7
    · have high : power ≤ 7#u32 := by exact hi
      obtain ⟨difference, sub, cast⟩ := low_index power lo hi
      have indexVal := indexWord_val (power.val - 1) (by omega)
      have schedule : powerAt (power.val - 1) = power.val := by
        have mapIndex : power.val - 1 < 7 := by omega
        generalize equation : power.val - 1 = index at mapIndex ⊢
        have correctPower : power.val = index + 1 := by omega
        rw [correctPower]
        interval_cases index <;> decide
      have correctTable := entries (power.val - 1) (by omega)
      rw [schedule] at correctTable
      have present : power.val ∈ powers := by
        simp only [powers, List.mem_cons, List.not_mem_nil, or_false]
        omega
      simp only [bulksketch.field.frobenius.lookup, low, high, ite_true,
        sub, bind_ok, cast, core.result.Result.expect, present]
      exact lookup_branch tables normal _ (by rw [indexVal]; omega) _ (by simpa only [indexVal] using correctTable) word
    · have high : ¬power ≤ 7#u32 := by exact hi
      simp only [bulksketch.field.frobenius.lookup, low, high, ite_true, ite_false]
      split
      · change _ = Result.ok (if 15 ∈ powers then
          some (⟨iterateSquare 15 word.bv⟩ : U64) else none)
        rw [ite_eq_left (show 15 ∈ powers by decide)]
        rw [show bulksketch.field.frobenius.lookup_loop1 = bulksketch.field.frobenius.lookup_loop0 from rfl]
        exact lookup_branch tables normal 7#usize (by simp) 15 (entries 7 (by decide)) word
      · change _ = Result.ok (if 31 ∈ powers then
          some (⟨iterateSquare 31 word.bv⟩ : U64) else none)
        rw [ite_eq_left (show 31 ∈ powers by decide)]
        rw [show bulksketch.field.frobenius.lookup_loop2 = bulksketch.field.frobenius.lookup_loop0 from rfl]
        exact lookup_branch tables normal 8#usize (by simp) 31 (entries 8 (by decide)) word
      · rename_i notFifteen notThirtyOne
        have present : power.val ∉ powers := by
          have h15 : power.val ≠ 15 := fun h => notFifteen (UScalar.eq_of_val_eq h)
          have h31 : power.val ≠ 31 := fun h => notThirtyOne (UScalar.eq_of_val_eq h)
          simp only [powers, List.mem_cons, List.not_mem_nil, or_false, not_or]
          omega
        simp [present]
  · have zero : power = 0#u32 := UScalar.eq_of_val_eq (by change power.val = 0; omega)
    subst power
    rfl

theorem inverse21_of_table (correct : InverseTableRefines) (word : U64) :
    bulksketch.field.frobenius.inverse21 word =
      Result.ok (⟨iterateSquare 21 word.bv⟩ : U64) := by
  obtain ⟨table, init, entries⟩ := correct
  have normal : bulksketch.field.frobenius.inverse21.TABLE = .ok table := by
    rw [bulksketch.field.frobenius.inverse21.TABLE, init]
  simp only [bulksketch.field.frobenius.inverse21, normal, bind_ok, lift]
  rw [show bulksketch.field.frobenius.inverse21_loop = bulksketch.field.frobenius.lookup_loop0 from rfl]
  exact start_scan table 21 entries word

end BulksketchBridge.FrobeniusTable
