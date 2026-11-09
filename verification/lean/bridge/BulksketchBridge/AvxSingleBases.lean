import Arithmetic.AvxSingleBasesGenerated
import BulksketchBridge.AvxEncode18Powers
import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxSingleBases

open Aeneas Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open X86MaskedMemory AvxSquare
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2300000

abbrev Row := Array U64 8#usize

def shiftWord (id : U64) (offset : Nat) : U64 := ⟨id.bv >>> offset⟩
def sixIndex (id : U64) (offset : Nat) : Usize := UScalar.cast .Usize (shiftWord id offset &&& 63#u64)
def fiveIndex (id : U64) (offset : Nat) : Usize := UScalar.cast .Usize (shiftWord id offset &&& 31#u64)
def lastIndex (id : U64) : Usize := UScalar.cast .Usize (shiftWord id 59)

def sixRow (table : InsertionBases) (chunk index : Nat) : Row :=
  (table.six.val[chunk]!).val[index]!

def fiveRow (table : InsertionBases) (chunk index : Nat) : Row :=
  (table.five.val[chunk]!).val[index]!

def combine (v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 : Word512) : Word512 :=
  xorRegister
    (xorRegister (xorRegister v0 (xorRegister v1 v2)) (xorRegister v3 (xorRegister v4 v5)))
    (xorRegister (xorRegister v6 (xorRegister v7 v8)) (xorRegister v9 v10))

def expected (table : InsertionBases) (id : U64) : Word512 :=
  combine
    (loadWords (sixRow table 0 (sixIndex id 0).val).to_slice)
    (loadWords (sixRow table 1 (sixIndex id 6).val).to_slice)
    (loadWords (sixRow table 2 (sixIndex id 12).val).to_slice)
    (loadWords (sixRow table 3 (sixIndex id 18).val).to_slice)
    (loadWords (sixRow table 4 (sixIndex id 24).val).to_slice)
    (loadWords (sixRow table 5 (sixIndex id 30).val).to_slice)
    (loadWords (sixRow table 6 (sixIndex id 36).val).to_slice)
    (loadWords (sixRow table 7 (sixIndex id 42).val).to_slice)
    (loadWords (sixRow table 8 (sixIndex id 48).val).to_slice)
    (loadWords (fiveRow table 0 (fiveIndex id 54).val).to_slice)
    (loadWords (fiveRow table 1 (lastIndex id).val).to_slice)

private theorem shift_normal (id : U64) (count : I32)
    (positive : 0 ≤ count.val) (bound : count.toNat < 64) :
    (id >>> count : Result U64) = Result.ok (shiftWord id count.toNat) := by
  change UScalar.shiftRight_IScalar id count = _
  unfold UScalar.shiftRight_IScalar
  rw [ite_eq_left positive]
  unfold UScalar.shiftRight
  rw [ite_eq_left (show count.toNat < UScalarTy.U64.numBits from bound)]
  rfl

private theorem cast_small (word : U64) (room : word.val < 64) :
    (UScalar.cast .Usize word).val = word.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  change word.val < 2 ^ System.Platform.numBits
  rcases System.Platform.numBits_eq with platform | platform <;> rw [platform] <;> omega

theorem six_index_exact (id : U64) (offset : Nat) :
    (sixIndex id offset).val = (id.val >>> offset) % 64 := by
  have small : ((shiftWord id offset) &&& 63#u64).val < 64 := by
    change ((id.bv >>> offset) &&& (63 : BitVec 64)).toNat < 64
    rw [BitVec.toNat_and]
    rw [show (63 : BitVec 64).toNat = 63 from rfl]
    have bounded := Nat.and_le_right (n := (id.bv >>> offset).toNat) (m := 63)
    omega
  unfold sixIndex
  rw [cast_small _ small]
  change ((id.bv >>> offset) &&& (63 : BitVec 64)).toNat = _
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  exact Nat.and_two_pow_sub_one_eq_mod _ 6

theorem five_index_exact (id : U64) (offset : Nat) :
    (fiveIndex id offset).val = (id.val >>> offset) % 32 := by
  have small : ((shiftWord id offset) &&& 31#u64).val < 64 := by
    change ((id.bv >>> offset) &&& (31 : BitVec 64)).toNat < 64
    rw [BitVec.toNat_and]
    rw [show (31 : BitVec 64).toNat = 31 from rfl]
    have bounded := Nat.and_le_right (n := (id.bv >>> offset).toNat) (m := 31)
    omega
  unfold fiveIndex
  rw [cast_small _ small]
  change ((id.bv >>> offset) &&& (31 : BitVec 64)).toNat = _
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight]
  exact Nat.and_two_pow_sub_one_eq_mod _ 5

theorem last_index_exact (id : U64) :
    (lastIndex id).val = id.val >>> 59 ∧ (lastIndex id).val < 32 := by
  have value : (shiftWord id 59).val = id.val >>> 59 := BitVec.toNat_ushiftRight ..
  have room : (shiftWord id 59).val < 32 := by
    have bound : id.val < 2 ^ 64 := id.bv.isLt
    rw [value, Nat.shiftRight_eq_div_pow]
    omega
  unfold lastIndex
  rw [cast_small _ (by omega), value]
  exact ⟨rfl, value ▸ room⟩

private theorem array_read {α : Type} [Inhabited α] {n : Usize}
    (array : Array α n) (index : Usize) (bound : index.val < n.val) :
    Array.index_usize array index = .ok array.val[index.val]! := by
  have active : index.val < array.val.length := by rw [Array.property]; exact bound
  simp only [Array.index_usize, Array.getElem?_Usize_eq, List.getElem?_eq_getElem active,
    List.Inhabited_getElem_eq_getElem! _ _ active]

private theorem row_load (loadModel : Load) (law : LoadLaw loadModel) (row : Row) :
    loadModel row.to_slice = .ok (loadWords row.to_slice) := by
  apply law
  simp only [Slice.length, Array.val_to_slice, Array.property]
  rfl

private theorem six_outer (table : InsertionBases) (chunk : Usize) (i : Nat)
    (exact : chunk.val = i) (room : i < 9) :
    Array.index_usize table.six chunk = .ok table.six.val[i]! := by
  have read := array_read table.six chunk (by rw [exact]; exact room)
  rwa [exact] at read

private theorem five_outer (table : InsertionBases) (chunk : Usize) (i : Nat)
    (exact : chunk.val = i) (room : i < 2) :
    Array.index_usize table.five chunk = .ok table.five.val[i]! := by
  have read := array_read table.five chunk (by rw [exact]; exact room)
  rwa [exact] at read

private theorem six_inner (table : InsertionBases) (id : U64) (chunk offset : Nat) :
    Array.index_usize table.six.val[chunk]! (sixIndex id offset) =
      .ok (sixRow table chunk (sixIndex id offset).val) := by
  apply array_read
  rw [six_index_exact]
  exact Nat.mod_lt _ (by decide)

private theorem five_inner (table : InsertionBases) (id : U64) (offset : Nat) :
    Array.index_usize table.five.val[0]! (fiveIndex id offset) =
      .ok (fiveRow table 0 (fiveIndex id offset).val) := by
  apply array_read
  rw [five_index_exact]
  exact Nat.mod_lt _ (by decide)

private theorem last_inner (table : InsertionBases) (id : U64) :
    Array.index_usize table.five.val[1]! (lastIndex id) =
      .ok (fiveRow table 1 (lastIndex id).val) := by
  apply array_read
  exact (last_index_exact id).2

/-- Exact original lookup and XOR schedule under the supplied static table and
admitted masked load value model. The generated shifts, casts and indices succeed. -/
def ActualSingleBases : Prop :=
  ∀ (tableModel : Result InsertionBases) (loadModel : Load), LoadLaw loadModel →
    ∀ table, tableModel = .ok table → ∀ id : U64,
      single_bases tableModel loadModel id = .ok (expected table id)

theorem single_bases_refines : ActualSingleBases := by
  intro tableModel loadModel law table lookup id
  have start : UScalar.cast .Usize (id &&& 63#u64) = sixIndex id 0 := by
    have shift0 : shiftWord id 0 = id := by cases id; simp [shiftWord]
    rw [sixIndex, shift0]
  have shift6 : (id >>> 6#i32 : Result U64) = Result.ok (shiftWord id 6) :=
    shift_normal id 6#i32 (by decide) (by decide)
  have shift12 : (id >>> 12#i32 : Result U64) = Result.ok (shiftWord id 12) :=
    shift_normal id 12#i32 (by decide) (by decide)
  have shift18 : (id >>> 18#i32 : Result U64) = Result.ok (shiftWord id 18) :=
    shift_normal id 18#i32 (by decide) (by decide)
  have shift24 : (id >>> 24#i32 : Result U64) = Result.ok (shiftWord id 24) :=
    shift_normal id 24#i32 (by decide) (by decide)
  have shift30 : (id >>> 30#i32 : Result U64) = Result.ok (shiftWord id 30) :=
    shift_normal id 30#i32 (by decide) (by decide)
  have shift36 : (id >>> 36#i32 : Result U64) = Result.ok (shiftWord id 36) :=
    shift_normal id 36#i32 (by decide) (by decide)
  have shift42 : (id >>> 42#i32 : Result U64) = Result.ok (shiftWord id 42) :=
    shift_normal id 42#i32 (by decide) (by decide)
  have shift48 : (id >>> 48#i32 : Result U64) = Result.ok (shiftWord id 48) :=
    shift_normal id 48#i32 (by decide) (by decide)
  have shift54 : (id >>> 54#i32 : Result U64) = Result.ok (shiftWord id 54) :=
    shift_normal id 54#i32 (by decide) (by decide)
  have shift59 : (id >>> 59#i32 : Result U64) = Result.ok (shiftWord id 59) :=
    shift_normal id 59#i32 (by decide) (by decide)
  have six0 := six_outer table 0#usize 0 (by simp) (by decide)
  have six1 := six_outer table 1#usize 1 (by simp) (by decide)
  have six2 := six_outer table 2#usize 2 (by simp) (by decide)
  have six3 := six_outer table 3#usize 3 (by simp) (by decide)
  have six4 := six_outer table 4#usize 4 (by simp) (by decide)
  have six5 := six_outer table 5#usize 5 (by simp) (by decide)
  have six6 := six_outer table 6#usize 6 (by simp) (by decide)
  have six7 := six_outer table 7#usize 7 (by simp) (by decide)
  have six8 := six_outer table 8#usize 8 (by simp) (by decide)
  have five0 := five_outer table 0#usize 0 (by simp) (by decide)
  have five1 := five_outer table 1#usize 1 (by simp) (by decide)
  have foldSix (offset : Nat) :
      UScalar.cast .Usize (shiftWord id offset &&& 63#u64) = sixIndex id offset := rfl
  have foldFive (offset : Nat) :
      UScalar.cast .Usize (shiftWord id offset &&& 31#u64) = fiveIndex id offset := rfl
  have foldLast : UScalar.cast .Usize (shiftWord id 59) = lastIndex id := rfl
  simp only [single_bases, bind_ok, lift, lookup, start,
    shift6, shift12, shift18, shift24, shift30, shift36, shift42, shift48, shift54, shift59,
    foldSix, foldFive, foldLast, six0, six1, six2, six3, six4, six5, six6, six7, six8,
    five0, five1, six_inner, five_inner, last_inner, row_load loadModel law, xorWords]
  rfl

end BulksketchBridge.AvxSingleBases
