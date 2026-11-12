import BulksketchBridge.RootTraceBasis
import BulksketchBridge.RootTraceField
import BulksketchBridge.Algebra.WordOps

namespace BulksketchBridge.RootTrace

open Aeneas.Std Algebra.Gf64 Polynomial
open BulksketchProofs.Field

set_option maxRecDepth 4096

private theorem clmul_two (bits : BitVec 64) :
    clmul128 bits 2 = (bits.setWidth 128 <<< (1 : Nat)) := by
  simp [clmul128, clmulPrefix, BitVec.getLsbD, Nat.testBit]

private theorem shifted_lo (bits : BitVec 64) :
    (bits.setWidth 128 <<< (1 : Nat)).setWidth 64 = bits <<< (1 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i small
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, small, decide_true, Bool.true_and]
  have earlier : i - 1 < 128 := by omega
  simp [earlier, show i < 128 by omega]

private theorem shifted_hi (bits : BitVec 64) :
    ((bits.setWidth 128 <<< (1 : Nat)) >>> (64 : Nat)).setWidth 64 = bits >>> (63 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i small
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
    small, decide_true, Bool.true_and]
  have inside : i + 64 - 1 < 128 := by omega
  have nonzero : 1 ≤ i + 64 := by omega
  have align : i + 64 - 1 = i + 63 := by omega
  simp [show 64 + i < 128 by omega, show 63 + i < 128 by omega]

theorem basis_next_field (word : U64) :
    toField (basisNext word).bv = toField word.bv * toField 2 := by
  rw [← toField_mul]
  congr 1
  unfold multiplyWord
  rw [clmul_two, shifted_lo, shifted_hi]
  let bits : BitVec 64 := word.bv
  let carry : BitVec 64 := bits >>> (63 : Nat)
  have small : carry.toNat < 2 := BitVec.toNat_ushiftRight_lt bits 63 (by decide)
  have values : carry = 0 ∨ carry = 1 := by
    by_cases zero : carry.toNat = 0
    · exact Or.inl (BitVec.eq_of_toNat_eq zero)
    · exact Or.inr (BitVec.eq_of_toNat_eq (show carry.toNat = 1 by omega))
  change (bits <<< (1 : Nat)) ^^^ (27 &&& (0 - carry)) = reduceFold64 (bits <<< (1 : Nat)) carry
  rcases values with zero | one
  · rw [zero, reduceFold64, BitVec.xor_assoc]
    congr 1
  · rw [one, reduceFold64, BitVec.xor_assoc]
    congr 1

theorem basis_word_field (seed : U64) (index : Nat) :
    toField (basisWord seed index).bv = toField (basisSeed seed).bv * toField 2 ^ index := by
  induction index with
  | zero => simp [basisWord]
  | succ n ih => rw [basisWord, basis_next_field, ih, pow_succ, mul_assoc]


private theorem generator_word : toField 2 = AdjoinRoot.root modulus := by
  unfold toField AdjoinRoot.root
  congr 1
  ext i
  rw [wordPolynomial_coeff, coeff_X]
  have bit : (2 : BitVec 64).getLsbD i = decide (1 = i) := by
    change (2 : Nat).testBit i = decide (1 = i)
    rw [show (2 : Nat) = 2 ^ 1 by decide, Nat.testBit_two_pow]
  rw [bit]
  by_cases eq : i = 1
  · simp [eq]
  · simp [eq, Ne.symm eq]

/-- For any distinct two field elements one of the 64 cached directions
separates their binary traces, even when the configured seed word is zero. -/
theorem some_cached_direction_separates
    (seed : U64) (left right : Field) (distinct : left ≠ right) :
    ∃ i < 64, Algebra.trace (ZMod 2) Field (toField (basisWord seed i).bv * left) ≠
      Algebra.trace (ZMod 2) Field (toField (basisWord seed i).bv * right) := by
  classical
  let pb := AdjoinRoot.powerBasis modulus_irreducible.ne_zero
  let factor := toField (basisSeed seed).bv * (left - right)
  have scaleNonzero : toField (basisSeed seed).bv ≠ 0 := by
    intro zero
    have h := toField_injective (zero.trans toField_zero.symm)
    exact seed_nonzero seed (U64.bv_eq_imp_eq _ _ h)
  have factorNonzero : factor ≠ 0 := mul_ne_zero scaleNonzero (sub_ne_zero.mpr distinct)
  by_contra! equal
  have linearZero : Algebra.traceForm (ZMod 2) Field factor = 0 := by
    apply pb.basis.ext
    intro index
    have dim : pb.dim = 64 := by
      rw [show pb.dim = modulus.natDegree from AdjoinRoot.powerBasis_dim _, modulus_natDegree]
    have bounded : index.val < 64 := by simpa only [← dim] using index.isLt
    have traced := equal index.val bounded
    rw [basis_word_field] at traced
    have generated : pb.gen = toField 2 := by
      rw [generator_word]
      exact AdjoinRoot.powerBasis_gen _
    rw [Algebra.traceForm_apply, pb.basis_eq_pow, generated]
    change Algebra.trace (ZMod 2) Field
      (toField (basisSeed seed).bv * (left - right) * toField 2 ^ index.val) = 0
    rw [show toField (basisSeed seed).bv * (left - right) * toField 2 ^ index.val =
      (toField (basisSeed seed).bv * toField 2 ^ index.val * left) -
      (toField (basisSeed seed).bv * toField 2 ^ index.val * right) by ring, map_sub]
    exact sub_eq_zero.mpr traced
  have zero := (traceForm_nondegenerate (ZMod 2) Field).1 factor
    (fun element => LinearMap.congr_fun linearZero element)
  exact factorNonzero zero


end BulksketchBridge.RootTrace
