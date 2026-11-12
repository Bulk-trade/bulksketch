import BulksketchBridge.DenseDivisionNormalized
import BulksketchBridge.DenseExactDivide
import BulksketchBridge.DenseGcdAlgebra

namespace BulksketchBridge.DenseDivision

open Aeneas.Std DenseCoefficient DenseGcd SliceKernels Algebra.Gf64 Polynomial
open bulksketch.backend.contract
open scoped BulksketchBridge.DenseMulReductionSpec

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

/-- The exact body equation needed to bind the two already-checked native
division consumers to the descending raw-word model. -/
def RefinesModel (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ (a b q rem : Slice U64) (raw : Slice BmDiscrepancy.Raw),
    0 < b.length → b[b.length - 1]! ≠ 0#u64 →
    a.length + 1 ≤ q.length → a.length + 1 ≤ rem.length → a.length + 1 ≤ raw.length →
    division DenseGcd.dictionary kernels a b q rem raw =
      .ok (expectedDivRem a b q rem raw (divisorInverse b[b.length - 1]!))

theorem model_gcd_law (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (modeled : RefinesModel division kernels) :
    DenseGcd.DivisionLaw division kernels := by
  intro a b q rem raw aNormal bNormal bPositive qRoom remRoom rawRoom
  let inv := divisorInverse b[b.length - 1]!
  let out := expectedDivRem a b q rem raw inv
  have call := modeled a b q rem raw bPositive (bNormal bPositive) qRoom remRoom rawRoom
  have widths := expected_widths a b q rem raw inv
  have normal := expected_remainder_normal a b q rem raw inv bPositive remRoom
  change out.1.2.val < b.length ∧
    (0 < out.1.2.val → (prefixSlice out.2.2.1 out.1.2.val)[out.1.2.val - 1]! ≠ 0#u64) at normal
  refine ⟨out.1.1, out.1.2, out.2.1, out.2.2.1, out.2.2.2, call,
    widths.1, widths.2.1, widths.2.2, normal.1, ?_⟩
  intro positive
  have remRoom' : out.1.2.val ≤ out.2.2.1.length := by
    have width := widths.2.1
    change out.2.2.1.length = rem.length at width
    rw [width]
    let count := min (b.length - 1) a.length
    have lengthRoom : count ≤ out.2.2.1.length := by rw [width]; unfold count; omega
    have bound := (output_length_normal out.2.2.1 count lengthRoom).1
    change out.1.2.val ≤ count at bound
    unfold count at bound
    omega
  have lengthExact : (prefixSlice out.2.2.1 out.1.2.val).length = out.1.2.val :=
    (RebuiltLfsr.prefix_length _ _).trans (Nat.min_eq_left remRoom')
  rw [lengthExact] at positive ⊢
  exact normal.2 positive

theorem model_gcd_meaning (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (modeled : RefinesModel division kernels) :
    DenseGcd.DivisionMeaning division kernels := by
  intro a b q rem raw qLen remLen qOut remOut rawOut aNormal bNormal bPositive qRoom remRoom rawRoom result
  let inv := divisorInverse b[b.length - 1]!
  have divisionEq := modeled a b q rem raw bPositive (bNormal bPositive) qRoom remRoom rawRoom
  have outputEq := Result.ok_injective (divisionEq.symm.trans result)
  have algebra := (model_meaning a b q rem raw inv bPositive qRoom remRoom rawRoom
    (divisor_inverse_law _ (bNormal bPositive))).1
  rw [outputEq] at algebra
  exact algebra

/-- The stock original exact-division wrapper receives its full exact
normalized frame from the descending model, conditional on the div/rem
body equation. No extra quotient clearing rule is assumed. -/
theorem modeled_exact_divide (division : DenseDivisionRuntime.DivRem) {K : Type}
    (kernels : BulkKernels K bulksketch.field.Gf64) (modeled : RefinesModel division kernels)
    (a b q rem : Slice U64) (raw : Slice BmDiscrepancy.Raw)
    (positive : 0 < b.length) (leading : b[b.length - 1]! ≠ 0#u64)
    (qRoom : a.length + 1 ≤ q.length) (remRoom : a.length + 1 ≤ rem.length)
    (rawRoom : a.length + 1 ≤ raw.length) :
    let out := expectedDivRem a b q rem raw (divisorInverse b[b.length - 1]!)
    bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into division
      DenseGcd.dictionary kernels a b q rem raw =
      if out.1.2 = 0#usize then .ok (some out.1.1, out.2.1, out.2.2.1, out.2.2.2)
      else .ok (none, cleared out.2.1 (a.length + 1), out.2.2.1, out.2.2.2) := by
  let inv := divisorInverse b[b.length - 1]!
  let out := expectedDivRem a b q rem raw inv
  have called := modeled a b q rem raw positive leading qRoom remRoom rawRoom
  have widths := expected_widths a b q rem raw inv
  apply DenseExactDivide.exact_divide_refines division DenseGcd.dictionary kernels a b q rem
    out.2.1 out.2.2.1 raw out.2.2.2 out.1.1 out.1.2 called
  intro _
  change a.length < out.2.1.length
  have width := widths.1
  change out.2.1.length = q.length at width
  rw [width]
  omega

private theorem field_zero_word (word : U64) (zero : toField word.bv = 0) : word = 0#u64 := by
  apply U64.bv_eq_imp_eq
  exact wordFieldEquiv.injective (zero.trans toField_zero.symm)

private theorem normal_polynomial_nonzero (words : Slice U64) (positive : 0 < words.length)
    (normal : words[words.length - 1]! ≠ 0#u64) : slicePolynomial words ≠ 0 := by
  intro zero
  have coefficient := slicePolynomial_coeff words (words.length - 1)
  rw [ite_eq_left (by omega), zero, coeff_zero] at coefficient
  exact normal (field_zero_word words[words.length - 1]! coefficient.symm)

/-- The original exact-division decision tests a genuine zero remainder:
the word length is zero exactly when the divisor divides the input. -/
theorem model_exact_iff_dvd (a b q rem : Slice U64) (raw : Slice BmDiscrepancy.Raw)
    (positive : 0 < b.length) (leading : b[b.length - 1]! ≠ 0#u64)
    (qRoom : a.length + 1 ≤ q.length) (remRoom : a.length + 1 ≤ rem.length)
    (rawRoom : a.length + 1 ≤ raw.length) :
    (expectedDivRem a b q rem raw (divisorInverse b[b.length - 1]!)).1.2.val = 0 ↔
      slicePolynomial b ∣ slicePolynomial a := by
  let inv := divisorInverse b[b.length - 1]!
  let out := expectedDivRem a b q rem raw inv
  let qPoly := slicePolynomial (prefixSlice out.2.1 out.1.1.val)
  let rPoly := slicePolynomial (prefixSlice out.2.2.1 out.1.2.val)
  have ⟨equation, small⟩ := model_meaning a b q rem raw inv positive qRoom remRoom rawRoom
    (divisor_inverse_law _ leading)
  change slicePolynomial a = qPoly * slicePolynomial b + rPoly at equation
  change rPoly.degree < (slicePolynomial b).degree at small
  change out.1.2.val = 0 ↔ _
  constructor
  · intro noRemainder
    have zero : rPoly = 0 := by
      unfold rPoly
      rw [noRemainder]
      ext i
      rw [prefix_coeff _ _ _ (Nat.zero_le _), coeff_zero, ite_eq_right (Nat.not_lt_zero _)]
    rw [equation, zero, add_zero]
    exact dvd_mul_left _ _
  · intro divides
    have rEq : rPoly = slicePolynomial a - qPoly * slicePolynomial b := by
      rw [equation, add_sub_cancel_left]
    have factor : slicePolynomial b ∣ rPoly := by
      rw [rEq]
      exact dvd_sub divides (dvd_mul_left _ _)
    have remainderZero : rPoly = 0 := eq_zero_of_dvd_of_degree_lt factor small
    by_contra nonzero
    have lengthPositive : 0 < out.1.2.val := Nat.pos_of_ne_zero nonzero
    have normal := (expected_remainder_normal a b q rem raw inv positive remRoom).2 lengthPositive
    let tail := prefixSlice out.2.2.1 out.1.2.val
    have width := (expected_widths a b q rem raw inv).2.1
    let count := min (b.length - 1) a.length
    have readRoom : count ≤ out.2.2.1.length := by rw [width]; unfold count; omega
    have lenBound : out.1.2.val ≤ count := (output_length_normal out.2.2.1 count readRoom).1
    have prefixRoom := lenBound.trans readRoom
    have tailLen : tail.length = out.1.2.val :=
      (RebuiltLfsr.prefix_length _ _).trans (Nat.min_eq_left prefixRoom)
    have lastNonzero : tail[tail.length - 1]! ≠ 0#u64 := by
      rw [tailLen]
      exact normal
    exact normal_polynomial_nonzero tail (tailLen.symm ▸ lengthPositive) lastNonzero remainderZero

end BulksketchBridge.DenseDivision
