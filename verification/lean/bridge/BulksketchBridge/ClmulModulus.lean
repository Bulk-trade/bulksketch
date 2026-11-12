import BulksketchProofs.Field.CLMul
import BulksketchProofs.Field.Reduction

namespace BulksketchBridge.ClmulModulus

open BulksketchProofs.Field

/-- The modulus low word contributes precisely coefficients 0, 1, 3 and 4. -/
theorem clmul128_modulus_low (high : BitVec 64) :
    clmul128 high 27#64 = fold128 high := by
  have zeroTail (count : Nat) : clmulPrefix high 0#64 count = 0 := by
    induction count with
    | zero => rfl
    | succ count ih => simp [clmulPrefix, ih]
  change clmulPrefix high 27#64 (5 + 59) = _
  rw [clmulPrefix_append, show (27#64 : BitVec 64) >>> 5 = 0#64 by decide, zeroTail]
  rw [show ((0 : BitVec 128) <<< 5) = 0#128 by decide, BitVec.xor_zero]
  simp [clmulPrefix, fold128]

theorem clmul128_modulus_low_word (high : BitVec 64) :
    (clmul128 high 27#64).setWidth 64 = fold64 high := by
  rw [clmul128_modulus_low, fold128_split]
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  simp [bound]

theorem clmul128_modulus_high_word (high : BitVec 64) :
    ((clmul128 high 27#64) >>> 64).setWidth 64 = overflow64 high := by
  rw [clmul128_modulus_low, fold128_split]
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  have inside : 64 + index < 128 := by omega
  simp [bound, inside]

end BulksketchBridge.ClmulModulus
