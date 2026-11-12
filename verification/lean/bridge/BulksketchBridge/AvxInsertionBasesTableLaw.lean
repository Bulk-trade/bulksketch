import BulksketchBridge.AvxInsertionBasesBitCells
import BulksketchBridge.AvxSingleBasesField
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

namespace BulksketchBridge.AvxInsertionBases

open Aeneas.Std Algebra.Gf64
open AvxSingleBases
open ClosedLeafAdvance (usizeWord word_val)
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2600000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

def oneAt (i : Nat) : BitVec 64 := (1 : BitVec 64) <<< i

private theorem bit_oneAt (i j : Nat) (bound : j < 64) :
    (oneAt i).getLsbD j = decide (i = j) := by
  unfold oneAt
  simp only [BitVec.getLsbD_shiftLeft, bound, decide_true, Bool.true_and]
  by_cases equal : i = j
  · subst j; simp
  · by_cases earlier : j < i
    · simp [equal, earlier]
    · simp [equal, earlier, show j - i ≠ 0 by omega]

private theorem mask_is_pow (shift : Usize) (room : shift.val < 6) : (bitMask shift).val = 2 ^ shift.val := by
  have small : 2 ^ shift.val ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (by omega)
  have fits : 2 ^ shift.val < 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with bits | bits <;> rw [bits] <;> omega
  change ((1#usize).bv <<< shift.val).toNat = _
  have one : (1#usize).bv.toNat = 1 := by simp
  rw [BitVec.toNat_shiftLeft, one]
  rw [Nat.shiftLeft_eq, Nat.one_mul]
  exact Nat.mod_eq_of_lt fits

private theorem test_mask (value shift : Usize) (room : shift.val < 6) :
    value &&& bitMask shift ≠ 0#usize ↔ value.val.testBit shift.val = true := by
  have bits : (value &&& bitMask shift).val = value.val &&& 2 ^ shift.val := by
    change (value.bv &&& (bitMask shift).bv).toNat = _
    rw [BitVec.toNat_and]
    change value.val &&& (bitMask shift).val = _
    rw [mask_is_pow shift room]
  constructor
  · intro set
    by_cases selected : value.val.testBit shift.val = true
    · exact selected
    · exfalso
      have zero : value.val &&& 2 ^ shift.val = 0 := by
        apply Nat.eq_of_testBit_eq
        intro i
        rw [Nat.testBit_and, Nat.testBit_two_pow]
        by_cases equal : i = shift.val
        · subst i; simp_all
        · simp [Ne.symm equal]
      exact set (UScalar.eq_of_val_eq (by rw [bits, zero]; rfl))
  · intro selected zero
    have out : value.val &&& 2 ^ shift.val = 0 := by
      rw [← bits, zero]
      rfl
    have falseBit := congrArg (fun word : Nat => word.testBit shift.val) out
    simp only [Nat.testBit_and, Nat.testBit_two_pow_self, selected, Bool.and_self, Nat.zero_testBit] at falseBit
    contradiction

def prefixBits (word : BitVec 64) (count : Nat) : BitVec 64 :=
  word &&& BitVec.ofNat 64 (2 ^ count - 1)

private theorem prefix_bit (word : BitVec 64) (count i : Nat) (room : i < 64) :
    (prefixBits word count).getLsbD i = if i < count then word.getLsbD i else false := by
  unfold prefixBits
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_ofNat, room, decide_true, Bool.true_and, Nat.testBit_two_pow_sub_one]
  by_cases active : i < count <;> simp [active]

private theorem prefix_zero (word : BitVec 64) : prefixBits word 0 = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i room
  rw [prefix_bit _ _ _ room]
  simp

private theorem prefix_full (word : BitVec 64) : prefixBits word 64 = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro i room
  rw [prefix_bit _ _ _ room, ite_eq_left room]

private theorem prefix_succ (word : BitVec 64) (count : Nat) :
    prefixBits word (count + 1) = prefixBits word count ^^^
      (if word.getLsbD count then oneAt count else 0) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i room
  rw [prefix_bit _ _ _ room, BitVec.getLsbD_xor, prefix_bit _ _ _ room]
  by_cases selected : word.getLsbD count = true
  · rw [ite_eq_left selected, bit_oneAt _ _ room]
    by_cases equal : i = count
    · subst i
      simp [selected]
    · have same : i < count + 1 ↔ i < count := by omega
      simp [same, Ne.symm equal]
  · have off : word.getLsbD count = false := by cases h : word.getLsbD count <;> simp_all
    have zero : (0 : BitVec 64).getLsbD i = false := by simp
    rw [ite_eq_right selected, zero, Bool.xor_false]
    by_cases equal : i = count
    · subst i
      simp [off]
    · have same : i < count + 1 ↔ i < count := by omega
      simp [same]

private theorem frob_xor (lane : Fin 8) (a b : BitVec 64) :
    laneFrobenius lane (a ^^^ b) = laneFrobenius lane a + laneFrobenius lane b := by
  unfold laneFrobenius
  by_cases active : lane.val < 7
  · simp only [active, ite_true, toField_xor]
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact map_add (iterateFrobenius Field 2 (lane.val + 1)) _ _
  · simp [active]

private theorem frob_zero (lane : Fin 8) : laneFrobenius lane 0 = 0 := by
  unfold laneFrobenius
  split
  · rw [toField_zero, zero_pow (by positivity)]
  · rfl

theorem sum_prefix (lane : Fin 8) (word : BitVec 64) (count : Nat) :
    (∑ i ∈ Finset.range count, laneFrobenius lane (if word.getLsbD i then oneAt i else 0)) =
      laneFrobenius lane (prefixBits word count) := by
  induction count with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, prefix_zero]
    exact (frob_zero lane).symm
  | succ count ih => rw [Finset.sum_range_succ, ih, prefix_succ, frob_xor]

private theorem contribution_test (start width index bit : Nat)
    (indexRoom : index < 2 ^ width) (bitRoom : bit < 64) :
    (contribution start index).getLsbD bit = true ↔
      start ≤ bit ∧ bit < start + width ∧ index.testBit (bit - start) = true := by
  unfold contribution
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat, bitRoom, decide_true, Bool.true_and]
  by_cases startRoom : start ≤ bit
  · have first : ¬bit < start := by omega
    have small : bit - start < 64 := by omega
    simp only [first, decide_false, Bool.not_false, small, decide_true, Bool.true_and, startRoom, true_and]
    by_cases inRange : bit < start + width
    · simp [inRange]
    · have limit : 2 ^ width ≤ 2 ^ (bit - start) := Nat.pow_le_pow_right (by decide) (by omega)
      have off := Nat.testBit_lt_two_pow (indexRoom.trans_le limit)
      simp [inRange, off]
  · simp [startRoom, show bit < start by omega]

private theorem six_route_values (bit : Usize) (first : bit.val < 54) :
    (route bit).1.val = bit.val / 6 ∧ (route bit).2.1.val = bit.val % 6 ∧ (route bit).2.2.val = 64 := by
  unfold route
  rw [ite_eq_left first]
  exact ⟨word_val _ (by have := small_usize; omega), word_val _ (by have := small_usize; omega), by simp⟩

private theorem five_route_values (bit : Usize) (first : 54 ≤ bit.val) (room : bit.val < 64) :
    (route bit).1.val = (bit.val - 54) / 5 ∧ (route bit).2.1.val = (bit.val - 54) % 5 ∧ (route bit).2.2.val = 32 := by
  unfold route
  rw [ite_eq_right (by omega : ¬bit.val < 54)]
  exact ⟨word_val _ (by have := small_usize; omega), word_val _ (by have := small_usize; omega), by simp⟩

private theorem six_condition (chunk index bit : Nat) (chunkRoom : chunk < 9)
    (indexRoom : index < 64) (bitRoom : bit < 64) :
    let b := usizeWord bit
    let v := usizeWord index
    (b.val < 54 ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
      1 ≤ v.val ∧ v.val < (route b).2.2.val) ↔
      (contribution (6 * chunk) index).getLsbD bit = true := by
  let b := usizeWord bit
  let v := usizeWord index
  have bVal : b.val = bit := word_val _ (by have := small_usize; omega)
  have vVal : v.val = index := word_val _ (by have := small_usize; omega)
  change (b.val < 54 ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
      1 ≤ v.val ∧ v.val < (route b).2.2.val) ↔ _
  rw [contribution_test (6 * chunk) 6 index bit (by exact indexRoom) bitRoom]
  by_cases first : bit < 54
  · have firstVal : b.val < 54 := by rwa [bVal]
    obtain ⟨location, shift, count⟩ := six_route_values b firstVal
    have shiftRoom : (route b).2.1.val < 6 := by rw [shift, bVal]; omega
    rw [test_mask v _ shiftRoom, location, shift, count, bVal, vVal]
    constructor
    · rintro ⟨_, selected, position, _, _⟩
      have indexShift : bit - (6 * chunk) = bit % 6 := by omega
      exact ⟨by omega, by omega, by rwa [indexShift]⟩
    · rintro ⟨lower, upper, selected⟩
      have indexShift : bit % 6 = bit - (6 * chunk) := by omega
      have nonzero : 1 ≤ index := by
        by_contra empty
        have zero : index = 0 := by omega
        rw [zero, Nat.zero_testBit] at selected
        contradiction
      exact ⟨first, by rwa [indexShift], by omega, nonzero, indexRoom⟩
  · have noRoute : ¬ (b.val < 54) := by rwa [bVal]
    simp only [noRoute, false_and]
    constructor
    · intro impossible; exact impossible.elim
    · rintro ⟨lower, upper, _⟩
      omega

private theorem five_condition (chunk index bit : Nat) (chunkRoom : chunk < 2)
    (indexRoom : index < 32) (bitRoom : bit < 64) :
    let b := usizeWord bit
    let v := usizeWord index
    (54 ≤ b.val ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
      1 ≤ v.val ∧ v.val < (route b).2.2.val) ↔
      (contribution (54 + 5 * chunk) index).getLsbD bit = true := by
  let b := usizeWord bit
  let v := usizeWord index
  have bVal : b.val = bit := word_val _ (by have := small_usize; omega)
  have vVal : v.val = index := word_val _ (by have := small_usize; omega)
  change (54 ≤ b.val ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
      1 ≤ v.val ∧ v.val < (route b).2.2.val) ↔ _
  rw [contribution_test (54 + 5 * chunk) 5 index bit (by exact indexRoom) bitRoom]
  by_cases first : 54 ≤ bit
  · have firstVal : 54 ≤ b.val := by rwa [bVal]
    obtain ⟨location, shift, count⟩ := five_route_values b firstVal (by omega)
    have shiftRoom : (route b).2.1.val < 6 := by rw [shift, bVal]; omega
    rw [test_mask v _ shiftRoom, location, shift, count, bVal, vVal]
    constructor
    · rintro ⟨_, selected, position, _, _⟩
      have indexShift : bit - (54 + 5 * chunk) = (bit - 54) % 5 := by omega
      exact ⟨by omega, by omega, by rwa [indexShift]⟩
    · rintro ⟨lower, upper, selected⟩
      have indexShift : (bit - 54) % 5 = bit - (54 + 5 * chunk) := by omega
      have nonzero : 1 ≤ index := by
        by_contra empty
        have zero : index = 0 := by omega
        rw [zero, Nat.zero_testBit] at selected
        contradiction
      exact ⟨first, by rwa [indexShift], by omega, nonzero, indexRoom⟩
  · have noRoute : ¬ (54 ≤ b.val) := by rwa [bVal]
    simp only [noRoute, false_and]
    constructor
    · intro impossible; exact impossible.elim
    · rintro ⟨lower, upper, _⟩
      omega


private theorem six_contribution_value (chunk index bit : Nat) (lane : Fin 8)
    (chunkRoom : chunk < 9) (indexRoom : index < 64) (bitRoom : bit < 64) :
    sixContribution chunk lane.val (usizeWord index) (usizeWord bit) =
      laneFrobenius lane (if (contribution (6 * chunk) index).getLsbD bit then oneAt bit else 0) := by
  let b := usizeWord bit
  let v := usizeWord index
  have matchBit := six_condition chunk index bit chunkRoom indexRoom bitRoom
  have gate : (b.val < 54 ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
      1 ≤ v.val ∧ v.val < (route b).2.2.val ∧ lane.val < 7) ↔
      ((contribution (6 * chunk) index).getLsbD bit = true ∧ lane.val < 7) := by
    have splitGuard :
        (b.val < 54 ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
          1 ≤ v.val ∧ v.val < (route b).2.2.val) ↔ (contribution (6 * chunk) index).getLsbD bit = true := matchBit
    rw [← splitGuard]
    tauto
  have position : b.val = bit := word_val _ (by have := small_usize; omega)
  have word : (bitColumn b).bv = oneAt bit := by
    change ((1 : BitVec 64) <<< b.val) = _
    rw [position]
    rfl
  change sixContribution chunk lane.val v b = _
  simp only [sixContribution, gate]
  by_cases laneRoom : lane.val < 7
  · by_cases hit : (contribution (6 * chunk) index).getLsbD bit = true
    · simp only [hit, laneRoom, and_self, ite_true, laneFrobenius, square_times_field, word]
    · simp only [hit, laneRoom, Bool.false_eq_true, false_and, ite_false, frob_zero]
  · simp only [laneRoom, and_false, ite_false, laneFrobenius]

private theorem table_six (chunk index : Nat) (lane : Fin 8)
    (chunkRoom : chunk < 9) (indexRoom : index < 64) :
    toField (sixRow generatedTable chunk index).val[lane.val]!.bv =
      laneFrobenius lane (contribution (6 * chunk) index) := by
  let v := usizeWord index
  have vVal : v.val = index := word_val _ (by have := small_usize; omega)
  have start : (0#usize).val = 0 := by simp
  have initial : cell zeroTables.1 chunk v.val lane.val = 0#u64 := by
    unfold zeroTables cell
    dsimp only
    rw [FrobeniusTables.entry_repeat _ _ chunk (by exact chunkRoom),
      FrobeniusTables.entry_repeat _ _ v.val (by rw [vVal]; exact indexRoom),
      FrobeniusTables.entry_repeat _ _ lane.val (by exact lane.isLt)]
  have summed := bit_fold_six_field zeroTables 0#usize 64 chunk lane.val v (by simp)
  rw [initial, start] at summed
  have zero : toField (0#u64).bv = 0 := toField_zero
  simp only [zero, zero_add] at summed
  have word : (sixRow generatedTable chunk index).val[lane.val]! =
      cell (bitFold zeroTables 0#usize 64).1 chunk v.val lane.val := by
    rw [vVal]
    unfold sixRow generatedTable cell FrobeniusTables.entry
    rfl
  rw [word, summed, ← prefix_full (contribution (6 * chunk) index), ← sum_prefix lane]
  apply Finset.sum_congr rfl
  intro bit inRange
  exact six_contribution_value chunk index bit lane chunkRoom indexRoom (Finset.mem_range.mp inRange)

private theorem five_contribution_value (chunk index bit : Nat) (lane : Fin 8)
    (chunkRoom : chunk < 2) (indexRoom : index < 32) (bitRoom : bit < 64) :
    fiveContribution chunk lane.val (usizeWord index) (usizeWord bit) =
      laneFrobenius lane (if (contribution (54 + 5 * chunk) index).getLsbD bit then oneAt bit else 0) := by
  let b := usizeWord bit
  let v := usizeWord index
  have matchBit := five_condition chunk index bit chunkRoom indexRoom bitRoom
  have gate : (54 ≤ b.val ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
      1 ≤ v.val ∧ v.val < (route b).2.2.val ∧ lane.val < 7) ↔
      ((contribution (54 + 5 * chunk) index).getLsbD bit = true ∧ lane.val < 7) := by
    have splitGuard :
        (54 ≤ b.val ∧ v &&& bitMask (route b).2.1 ≠ 0#usize ∧ chunk = (route b).1.val ∧
          1 ≤ v.val ∧ v.val < (route b).2.2.val) ↔ (contribution (54 + 5 * chunk) index).getLsbD bit = true := matchBit
    rw [← splitGuard]
    tauto
  have position : b.val = bit := word_val _ (by have := small_usize; omega)
  have word : (bitColumn b).bv = oneAt bit := by
    change ((1 : BitVec 64) <<< b.val) = _
    rw [position]
    rfl
  change fiveContribution chunk lane.val v b = _
  simp only [fiveContribution, gate]
  by_cases laneRoom : lane.val < 7
  · by_cases hit : (contribution (54 + 5 * chunk) index).getLsbD bit = true
    · simp only [hit, laneRoom, and_self, ite_true, laneFrobenius, square_times_field, word]
    · simp only [hit, laneRoom, Bool.false_eq_true, false_and, ite_false, frob_zero]
  · simp only [laneRoom, and_false, ite_false, laneFrobenius]

private theorem table_five (chunk index : Nat) (lane : Fin 8)
    (chunkRoom : chunk < 2) (indexRoom : index < 32) :
    toField (fiveRow generatedTable chunk index).val[lane.val]!.bv =
      laneFrobenius lane (contribution (54 + 5 * chunk) index) := by
  let v := usizeWord index
  have vVal : v.val = index := word_val _ (by have := small_usize; omega)
  have start : (0#usize).val = 0 := by simp
  have initial : cell zeroTables.2 chunk v.val lane.val = 0#u64 := by
    unfold zeroTables cell
    dsimp only
    rw [FrobeniusTables.entry_repeat _ _ chunk (by exact chunkRoom),
      FrobeniusTables.entry_repeat _ _ v.val (by rw [vVal]; exact indexRoom),
      FrobeniusTables.entry_repeat _ _ lane.val (by exact lane.isLt)]
  have summed := bit_fold_five_field zeroTables 0#usize 64 chunk lane.val v (by simp)
  rw [initial, start] at summed
  have zero : toField (0#u64).bv = 0 := toField_zero
  simp only [zero, zero_add] at summed
  have word : (fiveRow generatedTable chunk index).val[lane.val]! =
      cell (bitFold zeroTables 0#usize 64).2 chunk v.val lane.val := by
    rw [vVal]
    unfold fiveRow generatedTable cell FrobeniusTables.entry
    rfl
  rw [word, summed, ← prefix_full (contribution (54 + 5 * chunk) index), ← sum_prefix lane]
  apply Finset.sum_congr rfl
  intro bit inRange
  exact five_contribution_value chunk index bit lane chunkRoom indexRoom (Finset.mem_range.mp inRange)

theorem generated_table_law : TableLaw generatedTable :=
  ⟨fun chunk room index bound lane => table_six chunk index lane room bound,
   fun chunk room index bound lane => table_five chunk index lane room bound⟩

theorem original_generator_table_law :
    ∃ table, bulksketch.backend.x86_vpclmul512.insertion_bases = .ok table ∧ TableLaw table :=
  ⟨generatedTable, insertion_bases_refines, generated_table_law⟩

theorem generator_supplies_bases (loadModel : AvxSquareRuntime.Load) (loadLaw : AvxSquare.LoadLaw loadModel) :
    AvxEncode18.BasesLaw (bulksketch.backend.x86_vpclmul512.single_bases
      bulksketch.backend.x86_vpclmul512.insertion_bases loadModel) :=
  original_bases_law _ loadModel loadLaw generatedTable insertion_bases_refines generated_table_law

end BulksketchBridge.AvxInsertionBases
