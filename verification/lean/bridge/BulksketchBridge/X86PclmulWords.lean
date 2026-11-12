import BulksketchBridge.X86PclmulSpec

namespace BulksketchBridge.X86Pclmul

open Aeneas Aeneas.Std Aeneas.Std.WP X86PclmulRuntime BulksketchProofs.Field
open bulksketch.backend.x86_pclmul
open bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic

private theorem little_endian_roundtrip (input : BitVec 64) :
    (BitVec.fromLEBytes input.toLEBytes).cast (by simp [BitVec.toLEBytes_length]) = input := by
  apply (BitVec.eq_iff _ _).mpr
  intro index bound
  rw [BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!]
  have bit := BitVec.toLEBytes_getElem!_testBit input (index / 8) (index % 8) (by omega)
  rw [show 8 * (index / 8) + index % 8 = index by omega] at bit
  exact bit

private theorem decode_bytes (bytes : List (BitVec 8)) (width : 8 * bytes.length = 64)
    (input : BitVec 64) (encoded : bytes = input.toLEBytes) :
    (BitVec.fromLEBytes bytes).cast width = input := by
  subst bytes
  exact little_endian_roundtrip input

private theorem roundtrip_array (bytes : Array U8 8#usize) (input : BitVec 64)
    (encoded : bytes.val = input.toLEBytes.map (@UScalar.mk .U8)) :
    (BitVec.fromLEBytes (bytes.val.map U8.bv)).cast (by simp) = input := by
  apply decode_bytes
  rw [encoded, List.map_map]
  simp [Function.comp_def]

private theorem unsigned_to_signed (input : U64) :
    (core.num.I64.from_le_bytes (core.num.U64.to_le_bytes input)).bv = input.bv :=
  roundtrip_array _ _ ((spec_ok (core.num.U64.to_le_bytes input)).mp (core.num.U64.to_le_bytes.step_spec input))

private theorem signed_to_unsigned (input : I64) :
    (core.num.U64.from_le_bytes (core.num.I64.to_le_bytes input)).bv = input.bv :=
  roundtrip_array _ _ ((spec_ok (core.num.I64.to_le_bytes input)).mp (core.num.I64.to_le_bytes.step_spec input))

theorem word_refines : WordRefines := by
  intro input
  simp only [word, unsignedBytes, signedFromBytes, moveIn, bind_ok, unsigned_to_signed]

theorem low_refines : LowRefines := by
  intro input
  simp only [low, moveOut, signedBytes, unsignedFromBytes, bind_ok]
  apply congrArg Result.ok
  apply U64.bv_eq_imp_eq
  exact signed_to_unsigned ⟨low64 input⟩

theorem words_refines : WordsRefines := by
  intro input
  have lowOriginal := low_refines input
  have lowShifted := low_refines (input >>> 64)
  have shifted : shiftBytes 8#i32 input = Result.ok (input >>> 64) := rfl
  simp only [words, shifted, lowOriginal, lowShifted, bind_ok]

theorem clmul_input_words (a b : U64) :
    clmul 0#i32 (a.bv.setWidth 128) (b.bv.setWidth 128) =
      Result.ok (clmul128 a.bv b.bv) := by
  simp [clmul, low64, BitVec.setWidth_setWidth_of_le]

theorem raw_product_refines : RawProductRefines := by
  intro a b
  have left := word_refines a
  have right := word_refines b
  have split := words_refines (clmul128 a.bv b.bv)
  simp only [raw_product, left, right, bind_ok, clmul_input_words, split, RawMul.expectedProduct]

theorem raw_mul_refines : RawMulRefines := by
  intro a b
  exact raw_product_refines a b

end BulksketchBridge.X86Pclmul
