import BulksketchBridge.FrobeniusConstChallenges
import BulksketchBridge.FrobeniusConstSource
import Mathlib.Tactic.IntervalCases

namespace BulksketchBridge.FrobeniusConst

open Aeneas Aeneas.Std BulksketchProofs.Field

set_option maxRecDepth 4096

/-- Every original byte read is in bounds; rebuilding the low eight bytes is
exact truncation to the canonical native field word. -/
theorem low_bytes_refines (input : U128) :
    (do
      let bytes ← lift (core.num.U128.to_le_bytes input)
      let b0 ← Array.index_usize bytes 0#usize
      let b1 ← Array.index_usize bytes 1#usize
      let b2 ← Array.index_usize bytes 2#usize
      let b3 ← Array.index_usize bytes 3#usize
      let b4 ← Array.index_usize bytes 4#usize
      let b5 ← Array.index_usize bytes 5#usize
      let b6 ← Array.index_usize bytes 6#usize
      let b7 ← Array.index_usize bytes 7#usize
      Result.ok (core.num.U64.from_le_bytes
        (Array.make 8#usize [b0, b1, b2, b3, b4, b5, b6, b7]))) =
      Result.ok (⟨input.bv.setWidth 64⟩ : U64) := by
  have readByte (index : Usize) (bounded : index.val < 16) :
      Array.index_usize (core.num.U128.to_le_bytes input) index =
        Result.ok (⟨input.bv.toLEBytes[index.val]!⟩ : U8) := by
    have listBound : index.val < input.bv.toLEBytes.length := by
      simpa only [BitVec.toLEBytes_length, UScalarTy.U128_numBits_eq] using bounded
    simp only [Array.index_usize, Array.getElem?_Usize_eq, core.num.U128.to_le_bytes,
      Array.from_val, List.getElem?_map]
    rw [List.getElem?_eq_getElem listBound]
    simp only [Option.map_some]
    congr 2
    exact List.Inhabited_getElem_eq_getElem! _ _ listBound
  simp only [lift, bind_ok, readByte 0#usize (by scalar_tac),
    readByte 1#usize (by scalar_tac), readByte 2#usize (by scalar_tac),
    readByte 3#usize (by scalar_tac), readByte 4#usize (by scalar_tac),
    readByte 5#usize (by scalar_tac), readByte 6#usize (by scalar_tac),
    readByte 7#usize (by scalar_tac)]
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  simp only [core.num.U64.from_le_bytes]
  apply (BitVec.eq_iff _ _).mpr
  intro index bound
  have small : index < 64 := by simpa only [UScalarTy.U64_numBits_eq] using bound
  rw [BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!, BitVec.getElem!_setWidth 64 input.bv index small]
  erw [Array.make_val]
  simp only [List.map_cons, List.map_nil, UScalar.bv_mk_apply]
  interval_cases index <;>
    simp only [Nat.reduceDiv, Nat.reduceMod, List.getElem!_cons_zero, List.getElem!_cons_succ] <;>
    exact BitVec.toLEBytes_getElem!_testBit input.bv _ _ (by decide)

/-- The actual original const-square body is total on every U64 and has the
same exact canonical remainder as the already verified polynomial square. -/
theorem square_refines : FrobeniusConstChallenges.actualConstSquareMatchesWord := by
  intro input
  have spread := spread_loop input 0 (by decide)
  have division := division_loop (spreadPrefix input.bv 64) 0 (by decide)
  change bulksketch.field.frobenius.square_loop0 input 0#u128 0#i32 = _ at spread
  change bulksketch.field.frobenius.square_loop1
      (⟨spreadPrefix input.bv 64⟩ : U128) 128#i32 (⟨polynomial⟩ : U128) = _ at division
  have shift64 : 1#u128 <<< 64#i32 = Result.ok (⟨(1 : BitVec 128) <<< 64⟩ : U128) := by
    have normal := shift_normal (1#u128) 64 (by change 64 < 128; decide) (by decide)
    have literal : counter 64 = 64#i32 := by rfl
    rw [literal] at normal
    simpa only [U128.ofNat_bv, UScalarTy.U128_numBits_eq, BitVec.ofNat_eq_ofNat] using normal
  have polynomialValue :
      ((⟨(1 : BitVec 128) <<< 64⟩ : U128) ||| 27#u128) = (⟨polynomial⟩ : U128) := by
    decide +kernel
  simp only [bulksketch.field.frobenius.square, spread, shift64, lift, bind_ok,
    polynomialValue, division]
  have low := low_bytes_refines (⟨divisionPrefix (spreadPrefix input.bv 64) 64⟩ : U128)
  simp only [lift, bind_ok] at low
  rw [low, spreadPrefix_complete, division_square_complete]
  simp

end BulksketchBridge.FrobeniusConst
