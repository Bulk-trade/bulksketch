import BulksketchBridge.FrobeniusTableSpec

namespace BulksketchBridge.FrobeniusTable

open BulksketchProofs.Field.Period

def nibble (input : BitVec 64) (row : Nat) : BitVec 4 :=
  (input >>> (4 * row)).setWidth 4

def lookupPrefix (power : Nat) (input : BitVec 64) (count : Nat) : BitVec 64 :=
  iterateSquare power (xorPrefix input (4 * count))

/-- A lookup step contributes precisely four new input coefficients. -/
theorem prefix_step (power : Nat) (input : BitVec 64) (count : Nat) :
    lookupPrefix power input (count + 1) = lookupPrefix power input count ^^^
      cell power count (nibble input count).toNat := by
  have bits : xorPrefix input (4 * (count + 1)) = xorPrefix input (4 * count) ^^^
      ((nibble input count).setWidth 64 <<< (4 * count)) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [xorPrefix_bits _ _ _ hi, BitVec.getLsbD_xor, xorPrefix_bits _ _ _ hi]
    simp only [nibble, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
      BitVec.getLsbD_ushiftRight, hi, decide_true, Bool.true_and]
    by_cases before : i < 4 * count
    · simp [before, show i < 4 * (count + 1) by omega]
    · have inside : 4 * count ≤ i := by omega
      have recombine : 4 * count + (i - 4 * count) = i := by omega
      have fits : i - 4 * count < 64 := by omega
      have same : i - 4 * count < 4 ↔ i < 4 * (count + 1) := by omega
      simp only [before, fits, same, decide_true, Bool.true_and,
        Bool.false_xor, ite_false]
      by_cases h : i < 4 * (count + 1) <;> simp [h, recombine]
  unfold lookupPrefix cell
  rw [bits, iterateSquare_xor]
  rw [BitVec.ofNat_toNat]

@[simp] theorem prefix_zero (power : Nat) (input : BitVec 64) :
    lookupPrefix power input 0 = 0 := iterateSquare_zero power

theorem prefix_complete (power : Nat) (input : BitVec 64) :
    lookupPrefix power input 16 = iterateSquare power input := by
  simp only [lookupPrefix, show 4 * 16 = 64 by decide, xorPrefix_complete]

end BulksketchBridge.FrobeniusTable
