import BulksketchBridge.X86LaneMaskSpec
import BulksketchBridge.RawMulTable

namespace BulksketchBridge.X86LaneMask

open Aeneas Aeneas.Std

private theorem low_bits (output : U8) (len : Nat) (admitted : len ≤ 8)
    (bits : ∀ lane, lane < 8 → output.bv.getLsbD lane = decide (lane < len)) :
    output.val = 2 ^ len - 1 := by
  have exactBits : output.bv = BitVec.ofNat 8 (2 ^ len - 1) := by
    apply BitVec.eq_of_getLsbD_eq
    intro lane bounded
    rw [bits lane bounded, BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
    simp only [bounded, decide_true, Bool.true_and]
  change output.bv.toNat = _
  rw [exactBits, BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  have powBound : 2 ^ len ≤ 2 ^ 8 := Nat.pow_le_pow_right (by decide) admitted
  have positive := Nat.two_pow_pos len
  omega

/-- Both source paths complete. The nonzero path shifts by at most seven and
sets exactly the selected lanes. The zero path avoids a full-width shift. -/
theorem mask_refines : ActualMaskReturnsLowLanes := by
  intro len admitted
  have eight : (8#usize).val = 8 := by simp
  have guard : len ≤ 8#usize := (UScalar.le_equiv _ _).mpr (by rwa [eight])
  by_cases zero : len = 0#usize
  · subst len
    refine ⟨0#u8, ?_, ?_, ?_⟩
    · simp [bulksketch.backend.x86_vpclmul512.mask, massert, guard]
    · simp
    · intro lane _
      simp
  · have positive : 0 < len.val := by
      by_contra! empty
      apply zero
      apply UScalar.eq_of_val_eq
      simp
      omega
    obtain ⟨amount, subtract, value, _⟩ := RawMulTable.normal_of_spec _ _
      (Usize.sub_spec (x := 8#usize) (y := len) (by rwa [eight]))
    rw [eight] at value
    obtain ⟨output, shifted, _, shiftedBits⟩ := RawMulTable.normal_of_spec _ _
      (U8.ShiftRight_spec core.num.U8.MAX amount (by omega))
    have bits (lane : Nat) (_bounded : lane < 8) :
        output.bv.getLsbD lane = decide (lane < len.val) := by
      rw [shiftedBits, BitVec.getLsbD_ushiftRight]
      change (BitVec.allOnes 8).getLsbD (amount.val + lane) = _
      rw [BitVec.getLsbD_allOnes, value]
      exact decide_eq_decide.mpr (by omega)
    refine ⟨output, ?_, low_bits output len.val admitted bits, bits⟩
    simp [bulksketch.backend.x86_vpclmul512.mask, massert, guard, zero, subtract, shifted]

end BulksketchBridge.X86LaneMask
