import BulksketchBridge.AvxSingleBases
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas

namespace BulksketchBridge.AvxSingleBases

open Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open Algebra.Gf64 X86MaskedMemory AvxSquare
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

noncomputable def laneFrobenius (lane : Fin 8) (word : BitVec 64) : Field :=
  if lane.val < 7 then toField word ^ (2 ^ (lane.val + 1)) else 0

def contribution (offset index : Nat) : BitVec 64 := BitVec.ofNat 64 index <<< offset

/-- The original static generator's mathematical postcondition, with
nine six-bit positions and two five-bit positions covering one word. -/
def TableLaw (table : InsertionBases) : Prop :=
  (∀ chunk < 9, ∀ index < 64, ∀ lane : Fin 8,
    toField (sixRow table chunk index).val[lane.val]!.bv =
      laneFrobenius lane (contribution (6 * chunk) index)) ∧
  (∀ chunk < 2, ∀ index < 32, ∀ lane : Fin 8,
    toField (fiveRow table chunk index).val[lane.val]!.bv =
      laneFrobenius lane (contribution (54 + 5 * chunk) index))

private theorem frobenius_xor (lane : Fin 8) (left right : BitVec 64) :
    laneFrobenius lane (left ^^^ right) = laneFrobenius lane left + laneFrobenius lane right := by
  unfold laneFrobenius
  by_cases active : lane.val < 7
  · simp only [active, ite_true, toField_xor]
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact map_add (iterateFrobenius Field 2 (lane.val + 1)) _ _
  · simp only [active, ite_false, add_zero]

theorem row_lane (row : Row) (lane : Fin 8) :
    flatten (loadWords row.to_slice) lane = row.val[lane.val]!.bv := by
  have width : row.to_slice.length = 8 := by
    simp only [Slice.length, Array.val_to_slice, Array.property]
    rfl
  have unfoldLoad : loadWords row.to_slice =
      unflatten (fun i => if i.val < row.to_slice.length then row.to_slice[i.val]!.bv else 0) := rfl
  rw [unfoldLoad, flatten_unflatten, ite_eq_left (by rw [width]; exact lane.isLt)]
  rw [Slice.getElem!_Nat_eq, Array.val_to_slice]

private theorem six_contribution (id : U64) (offset : Nat) :
    contribution offset (sixIndex id offset).val = ((id.bv >>> offset) &&& 63#64) <<< offset := by
  unfold contribution
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, six_index_exact, BitVec.toNat_and, BitVec.toNat_ushiftRight]
  have modFits : (id.val >>> offset) % 64 < 2 ^ 64 := (Nat.mod_lt _ (by decide)).trans (by decide)
  rw [Nat.mod_eq_of_lt modFits]
  exact (Nat.and_two_pow_sub_one_eq_mod _ 6).symm

private theorem five_contribution (id : U64) (offset : Nat) :
    contribution offset (fiveIndex id offset).val = ((id.bv >>> offset) &&& 31#64) <<< offset := by
  unfold contribution
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, five_index_exact, BitVec.toNat_and, BitVec.toNat_ushiftRight]
  have modFits : (id.val >>> offset) % 32 < 2 ^ 64 := (Nat.mod_lt _ (by decide)).trans (by decide)
  rw [Nat.mod_eq_of_lt modFits]
  exact (Nat.and_two_pow_sub_one_eq_mod _ 5).symm

private theorem last_contribution (id : U64) :
    contribution 59 (lastIndex id).val = (id.bv >>> 59) <<< 59 := by
  unfold contribution
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, (last_index_exact id).1, BitVec.toNat_ushiftRight]
  have room : id.val >>> 59 < 2 ^ 64 := (Nat.shiftRight_le _ _).trans_lt id.bv.isLt
  exact Nat.mod_eq_of_lt room

private theorem flatten_xor (a b : Word512) (lane : Fin 8) :
    flatten (xorRegister a b) lane = flatten a lane ^^^ flatten b lane := rfl

private theorem masked_part_bit (word : BitVec 64) (offset width bit : Nat) (inWord : bit < 64) :
    (((word >>> offset) &&& BitVec.ofNat 64 (2 ^ width - 1)) <<< offset).getLsbD bit =
      if offset ≤ bit ∧ bit < offset + width then word.getLsbD bit else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one, BitVec.getLsbD_ushiftRight]
  by_cases before : bit < offset
  · simp [before, show ¬offset ≤ bit by omega]
  · have indexEq : offset + (bit - offset) = bit := by omega
    by_cases inside : bit < offset + width
    · simp [inWord, before, indexEq, inside, show offset ≤ bit by omega,
        show bit - offset < 64 by omega, show bit - offset < width by omega]
    · simp [inWord, before, indexEq, inside, show ¬ bit - offset < width by omega]

private theorem last_part_bit (word : BitVec 64) (bit : Nat) (inWord : bit < 64) :
    ((word >>> 59) <<< 59).getLsbD bit =
      if 59 ≤ bit then word.getLsbD bit else false := by
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight]
  by_cases before : bit < 59
  · simp [before, show ¬59 ≤ bit by omega]
  · simp [before, inWord, show 59 ≤ bit by omega, show 59 + (bit - 59) = bit by omega]

private theorem partition (word : BitVec 64) :
    let part (offset : Nat) := ((word >>> offset) &&& 63#64) <<< offset
    let five := ((word >>> 54) &&& 31#64) <<< 54
    let last := (word >>> 59) <<< 59
    ((part 0 ^^^ (part 6 ^^^ part 12)) ^^^ (part 18 ^^^ (part 24 ^^^ part 30))) ^^^
      ((part 36 ^^^ (part 42 ^^^ part 48)) ^^^ (five ^^^ last)) = word := by
  dsimp only
  apply BitVec.eq_of_getLsbD_eq
  intro bit inWord
  have six (offset : Nat) :
      (((word >>> offset) &&& 63#64) <<< offset).getLsbD bit =
        if offset ≤ bit ∧ bit < offset + 6 then word.getLsbD bit else false :=
    masked_part_bit word offset 6 bit inWord
  have five : (((word >>> 54) &&& 31#64) <<< 54).getLsbD bit =
      if 54 ≤ bit ∧ bit < 54 + 5 then word.getLsbD bit else false :=
    masked_part_bit word 54 5 bit inWord
  simp only [BitVec.getLsbD_xor, six, five, last_part_bit word bit inWord]
  have ranges : bit < 6 ∨ (6 ≤ bit ∧ bit < 12) ∨ (12 ≤ bit ∧ bit < 18) ∨ (18 ≤ bit ∧ bit < 24) ∨
      (24 ≤ bit ∧ bit < 30) ∨ (30 ≤ bit ∧ bit < 36) ∨ (36 ≤ bit ∧ bit < 42) ∨
      (42 ≤ bit ∧ bit < 48) ∨ (48 ≤ bit ∧ bit < 54) ∨ (54 ≤ bit ∧ bit < 59) ∨ 59 ≤ bit := by omega
  rcases ranges with h | h | h | h | h | h | h | h | h | h | h <;> simp (disch := omega) only [ite_eq_left, ite_eq_right, Bool.false_xor, Bool.xor_false]

theorem expected_lanes (table : InsertionBases) (valid : TableLaw table) (id : U64) (lane : Fin 8) :
    toField (flatten (expected table id) lane) = laneFrobenius lane id.bv := by
  have six (chunk : Nat) (bound : chunk < 9) (offset : Nat) (pos : offset = 6 * chunk) :
      toField (sixRow table chunk (sixIndex id offset).val).val[lane.val]!.bv =
        laneFrobenius lane (contribution offset (sixIndex id offset).val) := by
    rw [valid.1 chunk bound _ (by rw [six_index_exact]; exact Nat.mod_lt _ (by decide)), ← pos]
  have five : toField (fiveRow table 0 (fiveIndex id 54).val).val[lane.val]!.bv =
      laneFrobenius lane (contribution 54 (fiveIndex id 54).val) :=
    valid.2 0 (by decide) _ (by rw [five_index_exact]; exact Nat.mod_lt _ (by decide)) _
  have last : toField (fiveRow table 1 (lastIndex id).val).val[lane.val]!.bv =
      laneFrobenius lane (contribution 59 (lastIndex id).val) :=
    valid.2 1 (by decide) _ (last_index_exact id).2 _
  simp only [expected, combine, flatten_xor, toField_xor, row_lane,
    six 0 (by decide) 0 rfl, six 1 (by decide) 6 rfl, six 2 (by decide) 12 rfl,
    six 3 (by decide) 18 rfl, six 4 (by decide) 24 rfl, six 5 (by decide) 30 rfl,
    six 6 (by decide) 36 rfl, six 7 (by decide) 42 rfl, six 8 (by decide) 48 rfl,
    five, last, ← frobenius_xor, six_contribution, five_contribution, last_contribution]
  exact congrArg (laneFrobenius lane) (partition id.bv)

theorem original_bases_law (tableModel : Result InsertionBases) (loadModel : Load) (law : LoadLaw loadModel)
    (table : InsertionBases) (lookup : tableModel = .ok table) (valid : TableLaw table) :
    AvxEncode18.BasesLaw (single_bases tableModel loadModel) := by
  intro id
  exact ⟨expected table id, single_bases_refines tableModel loadModel law table lookup id, expected_lanes table valid id⟩

end BulksketchBridge.AvxSingleBases
