import BulksketchProofs.Field.ReductionSpec
import BulksketchProofs.Generated.Reduce

/-!
# GF64 two-fold polynomial reduction

The definitions in this module are a handwritten bitvector model of the GF64
branch of `src/field/gf64.rs::reduce`. Theorems about this model are not a
Rust-to-Lean refinement proof. Source extraction and its trust boundary are
tracked separately.
-/

namespace BulksketchProofs.Field

private theorem xor_shuffle {w : Nat} (a b c d e f g : BitVec w) :
    a ^^^ (b ^^^ c) ^^^ (d ^^^ e) ^^^ (f ^^^ g) =
      (a ^^^ b ^^^ d ^^^ f) ^^^ (c ^^^ e ^^^ g) := by
  ac_rfl

private theorem xor_cancel_five {w : Nat} (a b c d e : BitVec w) :
    (a ^^^ c ^^^ d) ^^^ ((b ^^^ e) ^^^ ((c ^^^ e) ^^^ d)) = a ^^^ b := by
  calc
    (a ^^^ c ^^^ d) ^^^ ((b ^^^ e) ^^^ ((c ^^^ e) ^^^ d)) =
        (a ^^^ b) ^^^ ((c ^^^ c) ^^^ ((d ^^^ d) ^^^ (e ^^^ e))) := by ac_rfl
    _ = a ^^^ b := by simp

/-- Splitting a bounded 128-bit shift into its low word and high carry. -/
theorem widen_shift_left_split (word : BitVec 64) (n : Nat) (hn : n ≤ 64) :
    (word.setWidth 128 <<< n) =
      (word <<< n).setWidth 128 ^^^
        ((word >>> (64 - n)).setWidth 128 <<< 64) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hlo : i < 64
  · have hsub : i - n < 64 := by omega
    simp [hlo, hi, hsub]
  · have hge : 64 ≤ i := by omega
    have hsub : i - 64 < 64 := by omega
    have hn_le : n ≤ i := by omega
    have hidx : 64 - n + (i - 64) = i - n := by omega
    have hsub128 : i - n < 128 := by omega
    simp [hlo, hi, hge, hsub128,
      Nat.not_lt.mpr hn_le, hidx]

/-- The first fold has exactly the carry word computed by `overflow64`. -/
theorem fold128_split (high : BitVec 64) :
    fold128 high = (fold64 high).setWidth 128 ^^^
      ((overflow64 high).setWidth 128 <<< 64) := by
  simp only [fold128, fold64, overflow64, BitVec.setWidth_xor,
    BitVec.shiftLeft_xor_distrib]
  rw [widen_shift_left_split high 1 (by decide),
    widen_shift_left_split high 3 (by decide),
    widen_shift_left_split high 4 (by decide)]
  simp only [show 64 - 1 = 63 by decide, show 64 - 3 = 61 by decide,
    show 64 - 4 = 60 by decide]
  apply xor_shuffle

/-- No coefficient of the first carry exists at index four or above. -/
theorem overflow64_high_bits (high : BitVec 64) (i : Nat) (hi : 4 ≤ i) :
    (overflow64 high).getLsbD i = false := by
  simp only [overflow64, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  rw [BitVec.getLsbD_of_ge high (63 + i) (by omega),
    BitVec.getLsbD_of_ge high (61 + i) (by omega),
    BitVec.getLsbD_of_ge high (60 + i) (by omega)]
  rfl

/-- Folding the first carry cannot itself produce another high carry. -/
theorem overflow64_overflow64 (high : BitVec 64) :
    overflow64 (overflow64 high) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  change (((overflow64 high >>> 63) ^^^ (overflow64 high >>> 61) ^^^
    (overflow64 high >>> 60)).getLsbD i) = (0 : BitVec 64).getLsbD i
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight]
  rw [overflow64_high_bits high (63 + i) (by omega),
    overflow64_high_bits high (61 + i) (by omega),
    overflow64_high_bits high (60 + i) (by omega)]
  simp

/-- The second untruncated fold fits entirely in the low word. -/
theorem fold128_overflow64 (high : BitVec 64) :
    fold128 (overflow64 high) = (fold64 (overflow64 high)).setWidth 128 := by
  rw [fold128_split, overflow64_overflow64]
  simp

/-- Multiplication by the low modulus is linear over coefficient XOR. -/
theorem fold128_xor (left right : BitVec 64) :
    fold128 (left ^^^ right) = fold128 left ^^^ fold128 right := by
  simp only [fold128, BitVec.setWidth_xor, BitVec.shiftLeft_xor_distrib]
  ac_rfl

/-- The low-word fold is linear over coefficient XOR. -/
theorem fold64_xor (left right : BitVec 64) :
    fold64 (left ^^^ right) = fold64 left ^^^ fold64 right := by
  simp only [fold64, BitVec.shiftLeft_xor_distrib]
  ac_rfl

/-- The carry map is linear over coefficient XOR. -/
theorem overflow64_xor (left right : BitVec 64) :
    overflow64 (left ^^^ right) = overflow64 left ^^^ overflow64 right := by
  simp only [overflow64, BitVec.ushiftRight_xor_distrib]
  ac_rfl

/-- The quotient correction is its own inverse because a carry's carry is zero. -/
theorem quotient_correction_involutive (high : BitVec 64) :
    (high ^^^ overflow64 high) ^^^ overflow64 (high ^^^ overflow64 high) = high := by
  rw [overflow64_xor, overflow64_overflow64]
  simp [BitVec.xor_assoc]

/-- Reduction can be delayed until after arbitrary raw polynomial XOR sums. -/
theorem reduceFold64_xor (low₁ high₁ low₂ high₂ : BitVec 64) :
    reduceFold64 (low₁ ^^^ low₂) (high₁ ^^^ high₂) =
      reduceFold64 low₁ high₁ ^^^ reduceFold64 low₂ high₂ := by
  simp only [reduceFold64, fold64_xor, overflow64_xor]
  ac_rfl

private def highWord128 (word : BitVec 128) : BitVec 64 :=
  (word >>> 64).setWidth 64

private theorem highWord128_xor (left right : BitVec 128) :
    highWord128 (left ^^^ right) = highWord128 left ^^^ highWord128 right := by
  simp only [highWord128, BitVec.ushiftRight_xor_distrib, BitVec.setWidth_xor]

private theorem highWord128_widen (word : BitVec 64) :
    highWord128 (word.setWidth 128) = 0 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [highWord128, hi]

private theorem highWord128_shift64 (word : BitVec 64) :
    highWord128 (word.setWidth 128 <<< 64) = word := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hsmall : 64 + i < 128 := by omega
  simp [highWord128, hi, hsmall]

private theorem highWord128_join (low high : BitVec 64) :
    highWord128 (join128 low high) = high := by
  rw [join128, highWord128_xor, highWord128_widen, highWord128_shift64]
  simp

private theorem highWord128_modulusMultiple (quotient : BitVec 64) :
    highWord128 (modulusMultiple128 quotient) = quotient ^^^ overflow64 quotient := by
  rw [modulusMultiple128, highWord128_xor, highWord128_shift64, fold128_split,
    highWord128_xor, highWord128_widen, highWord128_shift64]
  simp

/-- Universal polynomial-division certificate for every 128-bit input.

The quotient is `high XOR overflow64 high`; `modulusMultiple128` is its
exact carry-less product with the degree-64 modulus. The remainder is a
64-bit word, so this identity supplies both a modulus multiple and a
canonical-degree remainder without enumerating any input words. -/
theorem reduction_division_certificate (low high : BitVec 64) :
    join128 low high =
      (reduceFold64 low high).setWidth 128 ^^^
        modulusMultiple128 (high ^^^ overflow64 high) := by
  simp only [modulusMultiple128, BitVec.setWidth_xor,
    BitVec.shiftLeft_xor_distrib, fold128_xor]
  rw [fold128_split high, fold128_overflow64 high]
  simp only [join128, reduceFold64, BitVec.setWidth_xor]
  exact (xor_cancel_five _ _ _ _ _).symm

/-- The certificate's bounded quotient and remainder are unique.

Together with `reduction_division_certificate`, this characterizes the
canonical remainder by polynomial division, independently of a selected
long-division execution order. -/
theorem reduction_certificate_unique (low high remainder quotient : BitVec 64)
    (certificate : join128 low high = remainder.setWidth 128 ^^^
      modulusMultiple128 quotient) :
    quotient = high ^^^ overflow64 high ∧ remainder = reduceFold64 low high := by
  have highEq := congrArg highWord128 certificate
  rw [highWord128_join, highWord128_xor, highWord128_widen,
    highWord128_modulusMultiple] at highEq
  have highEq' : high = quotient ^^^ overflow64 quotient :=
    highEq.trans BitVec.zero_xor
  have quotientEq : quotient = high ^^^ overflow64 high := by
    calc
      quotient = (quotient ^^^ overflow64 quotient) ^^^
          overflow64 (quotient ^^^ overflow64 quotient) :=
        (quotient_correction_involutive quotient).symm
      _ = high ^^^ overflow64 high := by rw [← highEq']
  refine ⟨quotientEq, ?_⟩
  rw [quotientEq] at certificate
  have widened := (BitVec.xor_left_inj _).mp
    (certificate.symm.trans (reduction_division_certificate low high))
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hsmall : i < 128 := by omega
  have bitEq := congrArg (fun word : BitVec 128 => word.getLsbD i) widened
  simpa only [BitVec.getLsbD_setWidth, hsmall, decide_true, Bool.true_and] using bitEq

/-- The AST-derived exact-source expression equals the grouped bitvector model.

This checks the generated Lean expression, not the AST translator's correctness
or the semantics of the Rust compilation chain. -/
theorem generated_reduce_eq_model (low high : BitVec 64) :
    BulksketchProofs.Generated.reduceGf64 low high = reduceFold64 low high := by
  simp only [BulksketchProofs.Generated.reduceGf64, reduceFold64, fold64,
    overflow64, BitVec.xor_assoc]

/-- The division certificate applies to the exact-source-derived Lean expression. -/
theorem generated_reduction_division_certificate (low high : BitVec 64) :
    join128 low high =
      (BulksketchProofs.Generated.reduceGf64 low high).setWidth 128 ^^^
        modulusMultiple128 (high ^^^ overflow64 high) := by
  rw [generated_reduce_eq_model]
  exact reduction_division_certificate low high

/-- Uniqueness of the exact-source-derived expression's bounded division result. -/
theorem generated_reduction_certificate_unique
    (low high remainder quotient : BitVec 64)
    (certificate : join128 low high = remainder.setWidth 128 ^^^
      modulusMultiple128 quotient) :
    quotient = high ^^^ overflow64 high ∧
      remainder = BulksketchProofs.Generated.reduceGf64 low high := by
  rw [generated_reduce_eq_model]
  exact reduction_certificate_unique low high remainder quotient certificate

/-- The exact-source-derived reduction expression is XOR-linear on all raw inputs. -/
theorem generated_reduction_xor (low₁ high₁ low₂ high₂ : BitVec 64) :
    BulksketchProofs.Generated.reduceGf64 (low₁ ^^^ low₂) (high₁ ^^^ high₂) =
      BulksketchProofs.Generated.reduceGf64 low₁ high₁ ^^^
        BulksketchProofs.Generated.reduceGf64 low₂ high₂ := by
  simp only [generated_reduce_eq_model]
  exact reduceFold64_xor low₁ high₁ low₂ high₂

/-- The AST-derived expression's remainder has no coefficients at degree 64 or above. -/
theorem generated_remainder_high_bits (low high : BitVec 64) (i : Nat)
    (hi : 64 ≤ i) :
    ((BulksketchProofs.Generated.reduceGf64 low high).setWidth 128).getLsbD i = false := by
  simp [BitVec.getLsbD_of_ge _ i hi]

end BulksketchProofs.Field
