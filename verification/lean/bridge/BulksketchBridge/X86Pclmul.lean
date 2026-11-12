import BulksketchBridge.X86PclmulWords
import BulksketchBridge.ClmulModulus
import BulksketchBridge.Gf64Reduce
import BulksketchBridge.Algebra.WordNative

namespace BulksketchBridge.X86Pclmul

open Aeneas Aeneas.Std X86PclmulRuntime BulksketchProofs.Field
open BulksketchBridge.Algebra.Gf64 BulksketchBridge.ClmulModulus
open bulksketch.backend.x86_pclmul
open bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic

private theorem clmul_high_modulus (input : Xmm) :
    clmul 1#i32 input ((27#u64 : U64).bv.setWidth 128) =
      Result.ok (clmul128 (high64 input) 27#64) := by
  have bit0 : (1#i32).bv.getLsbD 0 = true := rfl
  have bit4 : (1#i32).bv.getLsbD 4 = false := rfl
  simp [clmul, low64, bit0, bit4]

private theorem xor_interleave {width : Nat} (a b c d : BitVec width) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by ac_rfl

private theorem join_xor (lo hi low' high' : BitVec 64) :
    join128 lo hi ^^^ join128 low' high' = join128 (lo ^^^ low') (hi ^^^ high') := by
  simp only [join128, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]
  exact xor_interleave _ _ _ _

private theorem join_zero (lo : BitVec 64) : join128 lo 0 = lo.setWidth 128 := by
  change lo.setWidth 128 ^^^ ((0#64).setWidth 128 <<< 64) = _
  rw [show ((0#64).setWidth 128 <<< 64) = 0#128 from rfl, BitVec.xor_zero]

private theorem fold_register (input : Xmm) :
    input ^^^ fold128 (high64 input) ^^^ fold128 (overflow64 (high64 input)) =
      join128 (reduceFold64 (low64 input) (high64 input))
        (high64 input ^^^ overflow64 (high64 input)) := by
  let lo := low64 input
  let hi := high64 input
  change input ^^^ fold128 hi ^^^ fold128 (overflow64 hi) =
    join128 (reduceFold64 lo hi) (hi ^^^ overflow64 hi)
  have split : input = join128 lo hi := (join128_split input).symm
  have first : fold128 hi = join128 (fold64 hi) (overflow64 hi) := fold128_split hi
  have second : fold128 (overflow64 hi) = join128 (fold64 (overflow64 hi)) 0 :=
    (fold128_overflow64 hi).trans (join_zero _).symm
  calc
    _ = join128 lo hi ^^^ fold128 hi ^^^ fold128 (overflow64 hi) :=
      congrArg (fun word => word ^^^ fold128 hi ^^^ fold128 (overflow64 hi)) split
    _ = _ := by
      have xorZero (word : BitVec 64) : word ^^^ (0 : BitVec 64) = word := BitVec.xor_zero
      rw [first, second, join_xor, join_xor, xorZero]
      rfl

private theorem reduce_value (input : Xmm) :
    bulksketch.field.gf64.reduce dictionary ⟨⟨low64 input⟩, ⟨high64 input⟩⟩ =
      Result.ok (⟨reduceFold64 (low64 input) (high64 input)⟩ : U64) := by
  obtain ⟨output, normal, bits, _⟩ :=
    Gf64Reduce.reduce_refines ⟨⟨low64 input⟩, ⟨high64 input⟩⟩
  have exactWord : output = ⟨reduceFold64 (low64 input) (high64 input)⟩ :=
    U64.bv_eq_imp_eq output _ bits
  rw [normal, exactWord]

theorem reduced_refines : ReducedRefines := by
  intro carryless input
  cases carryless with
  | false =>
    have wordsNormal := words_refines input
    change words input = Result.ok (⟨⟨low64 input⟩, ⟨high64 input⟩⟩ :
      bulksketch.types.RawProduct) at wordsNormal
    have widened := word_refines (⟨reduceFold64 (low64 input) (high64 input)⟩ : U64)
    simp only [reduced, Bool.false_eq_true, ite_false, wordsNormal, bind_ok, reduce_value,
      widened, join_zero]
    rfl
  | true =>
    have bits : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#u32 := by
      simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
    have modulus : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MODULUS_LOW = 27#u64 := by
      simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.MODULUS_LOW]
    have normal := word_refines 27#u64
    have highFold := clmul128_modulus_high_word (high64 input)
    change high64 (clmul128 (high64 input) 27#64) = overflow64 (high64 input) at highFold
    simp only [reduced, ite_true, bits, bind_ok, modulus, normal, clmul_high_modulus]
    rw [highFold]
    simp only [clmul128_modulus_low, X86PclmulRuntime.xor, bind_ok]
    exact congrArg Result.ok (fold_register input)

private theorem low_join (lo hi : BitVec 64) : low64 (join128 lo hi) = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i bound
  simp [low64, join128, bound, show ¬ 64 ≤ i by omega]

theorem multiply_refines : MultiplyRefines := by
  intro carryless a b
  let product := clmul128 a.bv b.bv
  let remainder := reduceFold64 (low64 product) (high64 product)
  let upper := if carryless then high64 product ^^^ overflow64 (high64 product) else 0
  have left := word_refines a
  have right := word_refines b
  have reduction : reduced carryless dictionary product = Result.ok (join128 remainder upper) :=
    reduced_refines carryless product
  have read : low (join128 remainder upper) = Result.ok (⟨remainder⟩ : U64) := by
    rw [low_refines]
    exact congrArg Result.ok (congrArg (fun x : BitVec 64 => (⟨x⟩ : U64)) (low_join remainder upper))
  simp only [multiply, left, right, bind_ok, clmul_input_words]
  change (do let result ← reduced carryless dictionary product; low result) = _
  rw [reduction]
  simp only [Bind.bind, bind_ok, read]
  rfl

theorem mul_refines : MulRefines := by
  intro a b
  exact multiply_refines true a b

theorem square_refines : SquareRefines := by
  intro a
  have same : multiplyWord a.bv a.bv = (Square.expectedWord a).bv := by
    apply toField_injective
    rw [toField_mul]
    change toField a.bv * toField a.bv = toField (BulksketchProofs.Field.Period.squareWord a.bv)
    rw [toField_square, pow_two]
  change multiply true dictionary a a = _
  rw [multiply_refines, same]

end BulksketchBridge.X86Pclmul
