import Arithmetic.X86PclmulNextGenerated
import BulksketchBridge.X86Pclmul
import BulksketchBridge.X86PclmulInverseMath
import BulksketchBridge.FrobeniusLookup

namespace BulksketchBridge.X86Pclmul

open Aeneas Aeneas.Std Algebra.Gf64
open Inverse (multiplyNativeWord frobeniusNativeWord expectedFieldInverse)
open bulksketch.backend.x86_pclmul

def InverseRefines : Prop :=
  ∀ input : U64, inverse dictionary input = Result.ok (expectedFieldInverse input)

def InverseEntryRefines : Prop :=
  ∀ input : U64,
    Pclmul.Insts.BulksketchBackendContractArithmetic.inverse dictionary input =
      Result.ok (expectedFieldInverse input)

def Map7Refines : Prop :=
  ∀ input : U64,
    inverse.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call dictionary () input =
      Result.ok (frobeniusNativeWord input 7#u32)

private theorem lookup3 (input : U64) :
    bulksketch.field.frobenius.lookup input 3#u32 =
      Result.ok (some (frobeniusNativeWord input 3#u32)) := by
  have known : (3#u32).val ∈ FrobeniusTable.powers := by decide +kernel
  simpa only [known, ite_true, frobeniusNativeWord] using FrobeniusTable.lookup_refines input 3#u32

theorem map7_refines : Map7Refines := by
  intro input
  have known : (7#u32).val ∈ FrobeniusTable.powers := by decide +kernel
  have lookup : bulksketch.field.frobenius.lookup input 7#u32 =
      Result.ok (some (frobeniusNativeWord input 7#u32)) := by
    simpa only [known, ite_true, frobeniusNativeWord] using FrobeniusTable.lookup_refines input 7#u32
  simp only [inverse.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call, lookup, bind_ok,
    core.option.Option.expect, Result.ofOption]

private theorem inverse21_normal (input : U64) :
    bulksketch.field.frobenius.inverse21 input =
      Result.ok (frobeniusNativeWord input 21#u32) := FrobeniusTable.inverse21_refines input

private theorem mul_normal (carryless : Bool) (left right : U64) :
    multiply carryless dictionary left right = Result.ok (multiplyNativeWord left right) :=
  multiply_refines carryless left right

private theorem inverse_one : expectedFieldInverse (1#u64) = some 1#u64 := by
  have nonzero : (1#u64 : U64) ≠ 0#u64 := by decide
  rw [expectedFieldInverse, ite_eq_right nonzero]
  apply congrArg some
  apply U64.bv_eq_imp_eq
  apply toField_injective
  change toField (wordFieldEquiv.symm (toField (1 : BitVec 64))⁻¹) = toField (1 : BitVec 64)
  rw [toField_one, inv_one]
  exact wordFieldEquiv.apply_symm_apply 1

theorem inverse_refines : InverseRefines := by
  intro input
  have bits : bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = 64#u32 := by
    simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  have sameBits : (64#u32 != 64#u32) = false := rfl
  have oneNotZero : ¬ (1#u64 : U64) = 0#u64 := by decide
  by_cases zero : input = 0#u64
  · rw [zero]
    simp only [inverse, bits, bind_ok, sameBits, Bool.false_eq_true, ite_false, ite_true, expectedFieldInverse]
  · by_cases one : input = 1#u64
    · rw [one]
      simp only [inverse, bits, bind_ok, sameBits, Bool.false_eq_true, ite_false,
        oneNotZero, ite_true, inverse_one]
    · rw [← inverse_chain_field input zero]
      have map7 (a : U64) :
          inverse.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call dictionary () a =
            Result.ok (frobeniusNativeWord a 7#u32) := map7_refines a
      simp only [inverse, bits, bind_ok, sameBits,
        Bool.false_eq_true, ite_false, zero, one, mul_normal, lookup3,
        core.option.Option.expect, Result.ofOption, map7, inverse21_normal, inverseChainWord]

theorem inverse_entry_refines : InverseEntryRefines := by
  intro input
  exact inverse_refines input

end BulksketchBridge.X86Pclmul
