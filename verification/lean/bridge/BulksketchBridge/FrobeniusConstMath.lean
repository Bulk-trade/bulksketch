import BulksketchBridge.FrobeniusConstSpec
import BulksketchProofs.Field.Spread
import BulksketchProofs.Field.Reduction
import BulksketchProofs.Field.CLMul

namespace BulksketchBridge.FrobeniusConst

open BulksketchProofs.Field

set_option maxRecDepth 4096

theorem single_bit {width : Nat} (shift index : Nat) (positive : 0 < width) :
    ((1 : BitVec width) <<< shift).getLsbD index =
      decide (index = shift ∧ index < width) := by
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases equal : index = shift
  · subst index
    simp [positive]
  · have either : index < shift ∨ shift < index := by omega
    rcases either with before | after
    · simp [equal, before]
    · simp [equal, show ¬index - shift = 0 by omega]

/-- The source spread loop retains exactly the processed even coefficients. -/
theorem spreadPrefix_bits (input : BitVec 64) (count index : Nat) (bound : count ≤ 64)
    (indexBound : index < 128) :
    (spreadPrefix input count).getLsbD index =
      if index % 2 = 0 ∧ index / 2 < count then input.getLsbD (index / 2) else false := by
  induction count with
  | zero => simp [spreadPrefix]
  | succ count inductionHypothesis =>
    rw [spreadPrefix, BitVec.getLsbD_xor, inductionHypothesis (by omega)]
    by_cases selected : input.getLsbD count
    · simp only [selected, ite_true, single_bit (width := 128) _ _ (by decide)]
      by_cases same : index = 2 * count
      · subst index
        simp [indexBound, selected]
      · have unchanged : (index % 2 = 0 ∧ index / 2 < count + 1) ↔
            (index % 2 = 0 ∧ index / 2 < count) := by omega
        simp only [same, false_and, decide_false, Bool.xor_false, unchanged]
    · simp only [selected, Bool.false_eq_true, ite_false]
      by_cases same : index = 2 * count
      · subst index
        simp [selected]
      · have unchanged : (index % 2 = 0 ∧ index / 2 < count + 1) ↔
            (index % 2 = 0 ∧ index / 2 < count) := by omega
        simp only [unchanged]
        simp

theorem spreadPrefix_complete (input : BitVec 64) :
    spreadPrefix input 64 = rawSquare128 input := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bounded
  rw [spreadPrefix_bits input 64 index (by decide) bounded,
    rawSquare128_bits input index bounded]
  simp [show index / 2 < 64 by omega]

theorem widen_basis (index : Nat) (bound : index < 64) :
    ((1 : BitVec 64) <<< index).setWidth 128 = (1 : BitVec 128) <<< index := by
  apply BitVec.eq_of_getLsbD_eq
  intro slot slotBound
  rw [BitVec.getLsbD_setWidth, single_bit _ _ (by decide), single_bit _ _ (by decide)]
  by_cases same : slot = index
  · simp [same, bound]
  · simp [same]

/-- A single long-division XOR is the exact full polynomial multiple. -/
theorem polynomial_shift (index : Nat) (bound : index < 64) :
    polynomial <<< index = modulusMultiple128 ((1 : BitVec 64) <<< index) := by
  have polynomialBits : polynomial =
      ((1 : BitVec 128) <<< 64) ^^^ (1 : BitVec 128) ^^^
        ((1 : BitVec 128) <<< 1) ^^^ ((1 : BitVec 128) <<< 3) ^^^ ((1 : BitVec 128) <<< 4) := by
    decide +kernel
  rw [polynomialBits]
  simp only [modulusMultiple128, fold128, widen_basis index bound,
    BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add]
  simp only [Nat.add_comm]
  ac_rfl

/-- The cancellation polynomial has exactly one coefficient at or above its
selected leading degree. -/
theorem polynomial_shift_upper (shift slot : Nat) (_bound : shift < 64)
    (atLeast : 64 + shift ≤ slot) (slotBound : slot < 128) :
    (polynomial <<< shift).getLsbD slot = decide (slot = 64 + shift) := by
  have polynomialBits : polynomial =
      ((1 : BitVec 128) <<< 64) ^^^ (1 : BitVec 128) ^^^
        ((1 : BitVec 128) <<< 1) ^^^ ((1 : BitVec 128) <<< 3) ^^^ ((1 : BitVec 128) <<< 4) := by
    decide +kernel
  rw [polynomialBits]
  simp only [BitVec.shiftLeft_xor_distrib, ← BitVec.shiftLeft_add,
    BitVec.getLsbD_xor, single_bit _ _ (by decide : 0 < 128)]
  have noZero : slot ≠ shift := by omega
  have noOne : slot ≠ 1 + shift := by omega
  have noThree : slot ≠ 3 + shift := by omega
  have noFour : slot ≠ 4 + shift := by omega
  simp only [slotBound, and_true, noZero, noOne, noThree, noFour,
    decide_false, Bool.xor_false]

/-- Each long-division step clears its selected coefficient without changing
any already cleared higher coefficient. -/
theorem divisionPrefix_upper (input : BitVec 128) (count : Nat) (bound : count ≤ 64) :
    ∀ slot, 128 - count ≤ slot → (divisionPrefix input count).getLsbD slot = false := by
  induction count with
  | zero =>
    intro slot atLeast
    exact BitVec.getLsbD_of_ge input slot atLeast
  | succ count inductionHypothesis =>
    intro slot atLeast
    by_cases outside : 128 ≤ slot
    · exact BitVec.getLsbD_of_ge _ _ outside
    have slotBound : slot < 128 := by omega
    have countBound : count < 64 := by omega
    have shiftBound : 127 - count - 64 < 64 := by omega
    have leading : 64 + (127 - count - 64) = 127 - count := by omega
    rw [divisionPrefix, divisionStep]
    by_cases selected : (divisionPrefix input count).getLsbD (127 - count)
    · simp only [selected, ite_true, BitVec.getLsbD_xor]
      rw [polynomial_shift_upper _ _ shiftBound (by omega) slotBound, leading]
      by_cases same : slot = 127 - count
      · subst slot
        simp [selected]
      · rw [inductionHypothesis (by omega) slot (by omega)]
        simp [same]
    · simp only [selected, Bool.false_eq_true, ite_false]
      by_cases same : slot = 127 - count
      · simpa only [same, Bool.not_eq_true] using selected
      · exact inductionHypothesis (by omega) slot (by omega)

private theorem xor_exchange (a b c d : BitVec 128) :
    (a ^^^ b) ^^^ (c ^^^ d) = (a ^^^ c) ^^^ (b ^^^ d) := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  simp only [BitVec.getLsbD_xor]
  cases a.getLsbD index <;> cases b.getLsbD index <;>
    cases c.getLsbD index <;> cases d.getLsbD index <;> rfl

theorem modulusMultiple_xor (left right : BitVec 64) :
    modulusMultiple128 (left ^^^ right) = modulusMultiple128 left ^^^ modulusMultiple128 right := by
  simp only [modulusMultiple128, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib,
    fold128_xor]
  exact xor_exchange _ _ _ _

/-- At every prefix the original value equals the current remainder plus the
exact accumulated full polynomial multiple. -/
theorem divisionPrefix_certificate (input : BitVec 128) (count : Nat)
    (bound : count ≤ 64) :
    input = divisionPrefix input count ^^^ modulusMultiple128 (quotientPrefix input count) := by
  induction count with
  | zero => simp [divisionPrefix, quotientPrefix, modulusMultiple128, fold128]
  | succ count inductionHypothesis =>
    have previous := inductionHypothesis (by omega)
    rw [divisionPrefix, quotientPrefix]
    by_cases selected : (divisionPrefix input count).getLsbD (127 - count)
    · simp only [selected, ite_true, divisionStep]
      have shifted := polynomial_shift (127 - count - 64) (by omega)
      have shiftEq : 127 - count - 64 = 63 - count := by omega
      rw [shiftEq] at shifted
      rw [shiftEq, shifted, modulusMultiple_xor]
      calc
        input = divisionPrefix input count ^^^ modulusMultiple128 (quotientPrefix input count) := previous
        _ = (divisionPrefix input count ^^^ modulusMultiple128 ((1 : BitVec 64) <<< (63 - count))) ^^^
            (modulusMultiple128 (quotientPrefix input count) ^^^
              modulusMultiple128 ((1 : BitVec 64) <<< (63 - count))) := by
          have cancel : ∀ (a b c : BitVec 128), (a ^^^ c) ^^^ (b ^^^ c) = a ^^^ b := by
            intro a b c
            calc
              (a ^^^ c) ^^^ (b ^^^ c) = (a ^^^ b) ^^^ (c ^^^ c) := by ac_rfl
              _ = a ^^^ b := by simp
          exact (cancel _ _ _).symm
    · rw [divisionStep, ite_eq_right selected, ite_eq_right selected]
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.xor_zero] using previous

theorem divisionPrefix_complete (input : BitVec 128) :
    divisionPrefix input 64 =
      (reduceFold64 (input.setWidth 64) ((input >>> 64).setWidth 64)).setWidth 128 := by
  have fits : divisionPrefix input 64 = ((divisionPrefix input 64).setWidth 64).setWidth 128 := by
    apply BitVec.eq_of_getLsbD_eq
    intro slot slotBound
    by_cases lower : slot < 64
    · simp [lower, slotBound]
    · rw [divisionPrefix_upper input 64 (by decide) slot (by omega)]
      simp [lower, slotBound]
  have certificate := divisionPrefix_certificate input 64 (by decide)
  rw [fits] at certificate
  have split : input = join128 (input.setWidth 64) ((input >>> 64).setWidth 64) :=
    (BulksketchProofs.Field.join128_split input).symm
  have joinedCertificate := split.symm.trans certificate
  have exactRemainder := (reduction_certificate_unique _ _ _ _ joinedCertificate).2
  exact fits.trans (congrArg (fun word : BitVec 64 => word.setWidth 128) exactRemainder)

theorem join_low (low high : BitVec 64) :
    (join128 low high).setWidth 64 = low := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  simp only [BitVec.getLsbD_setWidth, bound, decide_true, Bool.true_and]
  exact join128_low_bits low high index bound

theorem join_high (low high : BitVec 64) :
    ((join128 low high >>> 64).setWidth 64) = high := by
  apply BitVec.eq_of_getLsbD_eq
  intro index bound
  simp only [BitVec.getLsbD_setWidth, bound, decide_true, Bool.true_and,
    BitVec.getLsbD_ushiftRight]
  exact join128_high_bits low high index bound

theorem division_square_complete (input : BitVec 64) :
    divisionPrefix (rawSquare128 input) 64 = (Period.squareWord input).setWidth 128 := by
  rw [divisionPrefix_complete, rawSquare128, join_low, join_high]
  rfl

end BulksketchBridge.FrobeniusConst
