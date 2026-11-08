import BulksketchBridge.Avx512RegisterChallenges
import BulksketchBridge.ClmulModulus

namespace BulksketchBridge.Avx512Register

open Aeneas.Std Aeneas.Std.Avx512Register BulksketchProofs.Field
open BulksketchBridge.Algebra.Gf64 (multiplyWord)
open BulksketchBridge.Avx512RegisterChallenges BulksketchBridge.ClmulModulus
open bulksketch.backend.x86_vpclmul512

theorem raw_refines : rawRefines := by
  intro a b
  simp only [raw, clmul, bind_ok,
    show (0#i32 : I32).bv.getLsbD 0 = false by decide,
    show (0#i32 : I32).bv.getLsbD 4 = false by decide,
    show (17#i32 : I32).bv.getLsbD 0 = true by decide,
    show (17#i32 : I32).bv.getLsbD 4 = true by decide]
  rfl

theorem reduce_shift_refines : reduceShiftRefines := by
  intro low high
  simp only [reduce_shift, shiftRight, xorWords, bind_ok,
    reduce_shift.closure.Insts.CoreOpsFunctionFnTuple__m512i__m512i.call, shiftLeft]
  congr 1
  funext pair half
  simp only [shiftedReduction, reduceFold64, fold64, overflow64,
    show (63#u32 : U32).val = 63 by decide, show (61#u32 : U32).val = 61 by decide,
    show (60#u32 : U32).val = 60 by decide, show (1#u32 : U32).val = 1 by decide,
    show (3#u32 : U32).val = 3 by decide, show (4#u32 : U32).val = 4 by decide]
  have carry :
      (high pair half >>> 63) ^^^ ((high pair half >>> 61) ^^^ (high pair half >>> 60)) =
        (high pair half >>> 63) ^^^ (high pair half >>> 61) ^^^ (high pair half >>> 60) := by
    ac_rfl
  rw [carry]
  ac_rfl

theorem reduce_cl_refines : reduceClRefines := by
  intro input
  simp only [reduce_cl, broadcast, clmul, xorWords, bind_ok]
  congr 1
  funext pair half
  cases half
  · change input pair false ^^^
      ((clmul128 (input pair true) 27#64).setWidth 64 ^^^
        (clmul128 (((clmul128 (input pair true) 27#64) >>> 64).setWidth 64) 27#64).setWidth 64) =
          reduceFold64 (input pair false) (input pair true)
    rw [clmul128_modulus_high_word, clmul128_modulus_low_word, clmul128_modulus_low_word]
    unfold reduceFold64
    ac_rfl
  · change input pair true ^^^
      (((clmul128 (input pair true) 27#64) >>> 64).setWidth 64 ^^^
        ((clmul128 (((clmul128 (input pair true) 27#64) >>> 64).setWidth 64) 27#64) >>> 64).setWidth 64) =
          input pair true ^^^ overflow64 (input pair true)
    simp only [clmul128_modulus_high_word, overflow64_overflow64]
    rw [show (0 : BitVec 64) = 0#64 by rfl, BitVec.xor_zero]

theorem multiply_refines : multiplyRefines := by
  intro cl a b
  unfold multiply
  rw [raw_refines a b, bind_ok]
  dsimp! only
  have shiftExact (low high : Word512) :
      reduce_shift low high = Result.ok (shiftedReduction low high) :=
    reduce_shift_refines low high
  have clExact (input : Word512) :
      reduce_cl input = Result.ok (carrylessReduction input) :=
    reduce_cl_refines input
  cases cl
  · simp only [Bool.false_eq_true, ite_false, unpack, bind_ok, shiftExact]
    congr 1
    funext pair half
    cases half <;> rfl
  · simp only [ite_true, clExact, bind_ok, unpack]
    congr 1
    funext pair half
    cases half <;> rfl

end BulksketchBridge.Avx512Register
