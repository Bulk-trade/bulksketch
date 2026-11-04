import BulksketchProofs.Field.CLMulSpec
import BulksketchProofs.Field.Spread

namespace BulksketchProofs.Field

/-- Every prefix has exactly the GF(2) convolution of its selected coefficients. -/
theorem clmulPrefix_bits (left right : BitVec 64) (count index : Nat)
    (hi : index < 128) :
    (clmulPrefix left right count).getLsbD index =
      clmulCoefficientPrefix left right index count := by
  induction count with
  | zero => simp [clmulPrefix, clmulCoefficientPrefix]
  | succ count ih =>
    simp only [clmulPrefix, clmulCoefficientPrefix, BitVec.getLsbD_xor, ih]
    have hsub : index - count < 128 := by omega
    cases right.getLsbD count
    · simp
    · by_cases hc : index < count
      · have hc' : ¬count ≤ index := by omega
        simp [BitVec.getLsbD_shiftLeft, hi, hsub, hc, hc',
          -BitVec.getLsbD_eq_getElem]
      · have hc' : count ≤ index := by omega
        simp [BitVec.getLsbD_shiftLeft, hi, hsub, hc, hc',
          -BitVec.getLsbD_eq_getElem]

/-- Exact coefficients for all inputs and every one of the 128 output positions. -/
theorem clmul128_bits (left right : BitVec 64) (index : Nat) (hi : index < 128) :
    (clmul128 left right).getLsbD index = clmulCoefficient left right index :=
  clmulPrefix_bits left right 64 index hi

/-- The product of two degree-at-most-63 polynomials has degree at most 126. -/
theorem clmulCoefficient_high (left right : BitVec 64) (index : Nat)
    (hi : 127 ≤ index) : clmulCoefficient left right index = false := by
  have prefixHigh (count : Nat) (hc : count ≤ 64) :
      clmulCoefficientPrefix left right index count = false := by
    induction count with
    | zero => rfl
    | succ count ih =>
      have hc' : count ≤ 64 := by omega
      have hindex : 64 ≤ index - count := by omega
      simp [clmulCoefficientPrefix, ih hc', BitVec.getLsbD_of_ge left _ hindex]
  exact prefixHigh 64 (by decide)

/-- In particular the top stored bit is always zero; no degree-127 term exists. -/
theorem clmul128_top_bit (left right : BitVec 64) :
    (clmul128 left right).getLsbD 127 = false := by
  rw [clmul128_bits left right 127 (by decide)]
  exact clmulCoefficient_high left right 127 (by decide)

/-- Agreement on the selected right coefficients gives equal prefix products. -/
theorem clmulPrefix_right_congr (left right₁ right₂ : BitVec 64) (count : Nat)
    (same : ∀ index, index < count → right₁.getLsbD index = right₂.getLsbD index) :
    clmulPrefix left right₁ count = clmulPrefix left right₂ count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clmulPrefix, clmulPrefix, ih (fun index hi => same index (by omega)),
      same count (by omega)]

/-- Split a polynomial product prefix into an old prefix and one shifted block. -/
theorem clmulPrefix_append (left right : BitVec 64) (offset count : Nat) :
    clmulPrefix left right (offset + count) =
      clmulPrefix left right offset ^^^
        (clmulPrefix left (right >>> offset) count <<< offset) := by
  induction count with
  | zero => simp [clmulPrefix]
  | succ count ih =>
    rw [Nat.add_succ, clmulPrefix, ih, clmulPrefix,
      BitVec.shiftLeft_xor_distrib]
    simp only [BitVec.getLsbD_ushiftRight]
    cases right.getLsbD (offset + count) <;>
      simp [← BitVec.shiftLeft_add, Nat.add_comm, BitVec.xor_assoc]

/-- Zero-extending a nibble preserves exactly the four selected coefficients. -/
theorem nibbleMultiple_extract (left right : BitVec 64) :
    nibbleMultiple left (right.setWidth 4) = clmulPrefix left right 4 := by
  apply clmulPrefix_right_congr
  intro index hi
  have h64 : index < 64 := by omega
  simp [hi, h64, -BitVec.getLsbD_eq_getElem]

/-- The source's next nibble contributes precisely the next four product terms. -/
theorem clmulPrefix_nibble_step (left right : BitVec 64) (count : Nat) :
    clmulPrefix left right (4 * (count + 1)) =
      clmulPrefix left right (4 * count) ^^^
        (nibbleMultiple left ((right >>> (4 * count)).setWidth 4) <<< (4 * count)) := by
  rw [nibbleMultiple_extract]
  have index : 4 * (count + 1) = 4 * count + 4 := by omega
  rw [index, clmulPrefix_append]

/-- Splitting and rejoining preserves every one of the 128 coefficient bits. -/
theorem join128_split (word : BitVec 128) :
    join128 (word.setWidth 64) ((word >>> 64).setWidth 64) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro index hi
  by_cases low : index < 64
  · rw [join128_low_bits _ _ index low]
    simp [low, -BitVec.getLsbD_eq_getElem]
  · have high : index - 64 < 64 := by omega
    have indexEq : index = 64 + (index - 64) := by omega
    rw [indexEq, join128_high_bits _ _ _ high]
    simp [high, hi, ← indexEq]

end BulksketchProofs.Field
