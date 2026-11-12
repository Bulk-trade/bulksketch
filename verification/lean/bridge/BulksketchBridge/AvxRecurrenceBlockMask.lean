import Arithmetic.AvxRecurrenceGenerated
import BulksketchBridge.X86LaneMask

namespace BulksketchBridge.AvxRecurrence

open Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxRecurrenceRuntime
open BulksketchBridge.X86MaskedMemory

def testWord (left right : Word512) : U8 :=
  ⟨BitVec.cast (by simp) (BitVec.ofBoolListLE (List.ofFn (laneTest left right)))⟩

def allOnes : Word512 := fun _ _ => (-1)#i64 |>.bv

def laneXor (left right : Word512) : Word512 :=
  fun pair half => left pair half ^^^ right pair half

theorem test_mask_normal (left right : Word512) :
    testMask left right = .ok (testWord left right) := rfl

theorem test_word_bit (left right : Word512) (lane : Fin 8) :
    (testWord left right).bv.getLsbD lane.val = laneTest left right lane := by
  simp only [testWord, UScalar.bv_mk_apply, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, lane.isLt, dite_true, Option.getD_some]

private theorem test_xor_at (expected actual : Word512) (pair : Fin 4) (half : Bool) :
    (testWord (laneXor expected actual) allOnes).bv.getLsbD (flatIndex pair half).val =
      decide (expected pair half ≠ actual pair half) := by
  rw [test_word_bit, laneTest, flatten_at, flatten_at]
  have ones : ((-1)#i64).bv = BitVec.allOnes 64 := by decide
  simp only [laneXor, allOnes, ones, BitVec.and_allOnes,
    show (0 : BitVec 64) = 0#64 from rfl]
  exact decide_eq_decide.mpr (not_congr BitVec.xor_eq_zero_iff)

theorem flat_index_surjective (lane : Fin 8) :
    ∃ pair : Fin 4, ∃ half : Bool, flatIndex pair half = lane := by
  refine ⟨⟨lane.val / 2, by omega⟩, decide (lane.val % 2 = 1), ?_⟩
  apply Fin.ext
  simp only [flatIndex, decide_eq_true_eq]
  split <;> omega

private theorem zero_word_bit (lane : Nat) : (UScalar.bv (0#u8)).getLsbD lane = false := by
  change (0#8).getLsbD lane = false
  exact BitVec.getLsbD_zero

/-- After the source low-lane mask, zero means equality on every live lane.
No property is needed of any inactive lane. -/
theorem masked_mismatch_zero_iff (expected actual : Word512) (mask : U8) (len : Nat)
    (bits : ∀ lane < 8, mask.bv.getLsbD lane = decide (lane < len)) :
    testWord (laneXor expected actual) allOnes &&& mask = 0#u8 ↔
      ∀ pair half, (flatIndex pair half).val < len → expected pair half = actual pair half := by
  constructor
  · intro zero pair half active
    let lane := flatIndex pair half
    have cleared := congrArg (fun word : U8 => (UScalar.bv word).getLsbD lane.val) zero
    rw [UScalar.bv_and, zero_word_bit] at cleared
    rw [BitVec.getLsbD_and, test_xor_at, bits lane.val lane.isLt,
      decide_eq_true active, Bool.and_true] at cleared
    exact not_not.mp (of_decide_eq_false cleared)
  · intro equal
    apply U8.bv_eq_imp_eq
    apply BitVec.eq_of_getLsbD_eq
    intro lane bounded
    obtain ⟨pair, half, laneEq⟩ := flat_index_surjective ⟨lane, bounded⟩
    have index : (flatIndex pair half).val = lane := congrArg Fin.val laneEq
    rw [UScalar.bv_and, zero_word_bit]
    rw [BitVec.getLsbD_and, bits lane bounded, ← index, test_xor_at]
    by_cases active : (flatIndex pair half).val < len
    · simp only [equal pair half active, ne_eq, not_true_eq_false, decide_false, Bool.false_and]
    · simp only [active, decide_false, Bool.and_false]

#print axioms masked_mismatch_zero_iff

end BulksketchBridge.AvxRecurrence
