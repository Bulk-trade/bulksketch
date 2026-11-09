import BulksketchBridge.RootDivideNative

namespace BulksketchBridge.RootDivide

open Aeneas Aeneas.Std Algebra.Gf64 DenseCoefficient RebuiltLfsr BmEntry SliceKernels Polynomial
open Aeneas.Std.RootDivideRuntime
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types
open bulksketch.poly.Dense.Insts.BulksketchPolyPolynomial (exact_divide_into)

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

private theorem normal_degree (words : Slice U64) (positive : 0 < words.length)
    (leading : words[words.length - 1]! ≠ 0#u64) :
    slicePolynomial words ≠ 0 ∧ (slicePolynomial words).natDegree = words.length - 1 := by
  have upper : (slicePolynomial words).natDegree ≤ words.length - 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i outside
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  have last : (slicePolynomial words).coeff (words.length - 1) ≠ 0 := by
    rw [slicePolynomial_coeff, ite_eq_left (by omega)]
    intro zero
    exact leading (U64.bv_eq_imp_eq _ _ (toField_injective (zero.trans toField_zero.symm)))
  refine ⟨?_, natDegree_eq_of_le_of_coeff_ne_zero upper last⟩
  intro zero
  exact last (by rw [zero, coeff_zero])

private theorem empty_prefix_poly (words : Slice U64) : slicePolynomial (prefixSlice words 0) = 0 := by
  ext i
  rw [prefix_coeff _ _ _ (Nat.zero_le _), coeff_zero, ite_eq_right (Nat.not_lt_zero _)]

/-- A successful exact division of two normalized nonzero inputs returns
    a nonempty normalized quotient and preserves the exact degree sum. -/
theorem exact_division_degree (a b q rem : Slice U64) (raw : Slice RawProduct)
    (aPositive : 0 < a.length) (bPositive : 0 < b.length)
    (aLeading : a[a.length - 1]! ≠ 0#u64) (bLeading : b[b.length - 1]! ≠ 0#u64)
    (qRoom : a.length + 1 ≤ q.length) (remRoom : a.length + 1 ≤ rem.length)
    (rawRoom : a.length + 1 ≤ raw.length) (length : Usize)
    (success : (exactDivisionResult a b q rem raw).1 = some length) :
    let written := (exactDivisionResult a b q rem raw).2.1
    let quotient := prefixSlice written length.val
    0 < length.val ∧ length.val ≤ written.length ∧ quotient[length.val - 1]! ≠ 0#u64 ∧
    b.length - 1 + (length.val - 1) = a.length - 1 ∧
    slicePolynomial a = slicePolynomial quotient * slicePolynomial b := by
  let inverse := DenseDivision.divisorInverse b[b.length - 1]!
  let out := DenseDivision.expectedDivRem a b q rem raw inverse
  have returned : (exactDivisionResult a b q rem raw) =
      if out.1.2 = 0#usize then (some out.1.1, out.2.1, out.2.2.1, out.2.2.2)
      else (none, DenseDivision.cleared out.2.1 (a.length + 1), out.2.2.1, out.2.2.2) := rfl
  rw [returned] at success
  by_cases zero : out.1.2 = 0#usize
  · simp only [zero, ite_true] at success
    have size := Option.some.inj success
    subst length
    have decomposition := (DenseDivision.model_meaning a b q rem raw inverse bPositive
      qRoom remRoom rawRoom (DenseDivision.divisor_inverse_law _ bLeading)).1
    change slicePolynomial a =
      slicePolynomial (prefixSlice out.2.1 out.1.1.val) * slicePolynomial b +
        slicePolynomial (prefixSlice out.2.2.1 out.1.2.val) at decomposition
    have remZero : out.1.2.val = 0 := by rw [zero]; rfl
    rw [remZero, empty_prefix_poly, add_zero] at decomposition
    obtain ⟨aNonzero, aDegree⟩ := normal_degree a aPositive aLeading
    obtain ⟨bNonzero, bDegree⟩ := normal_degree b bPositive bLeading
    have qNonzero : slicePolynomial (prefixSlice out.2.1 out.1.1.val) ≠ 0 := by
      intro empty
      rw [empty, zero_mul] at decomposition
      exact aNonzero decomposition
    have qPositive : 0 < out.1.1.val := by
      apply Nat.pos_of_ne_zero
      intro empty
      apply qNonzero
      rw [empty, empty_prefix_poly]
    have qWidth : out.2.1.length = q.length := (DenseDivision.expected_widths a b q rem raw inverse).1
    have normal := DenseDivision.output_length_normal out.2.1 (a.length + 1) (by rwa [qWidth])
    change out.1.1.val ≤ a.length + 1 ∧
      (0 < out.1.1.val → (prefixSlice out.2.1 out.1.1.val)[out.1.1.val - 1]! ≠ 0#u64) at normal
    have fits : out.1.1.val ≤ out.2.1.length := normal.1.trans (by rwa [qWidth])
    have prefixLength : (prefixSlice out.2.1 out.1.1.val).length = out.1.1.val :=
      (prefix_length _ _).trans (Nat.min_eq_left fits)
    have leading := normal.2 qPositive
    have qDegree := (normal_degree (prefixSlice out.2.1 out.1.1.val) (by rwa [prefixLength])
      (by rwa [prefixLength])).2
    rw [prefixLength] at qDegree
    have degrees := congrArg Polynomial.natDegree decomposition
    rw [aDegree, Polynomial.natDegree_mul'
      (mul_ne_zero (leadingCoeff_ne_zero.mpr qNonzero) (leadingCoeff_ne_zero.mpr bNonzero)),
      qDegree, bDegree] at degrees
    have conservation : b.length - 1 + (out.1.1.val - 1) = a.length - 1 := by
      omega
    have writtenEq : (exactDivisionResult a b q rem raw).2.1 = out.2.1 := by
      rw [returned, ite_eq_left zero]
    dsimp only
    rw [writtenEq]
    exact ⟨qPositive, fits, leading, conservation, decomposition⟩
  · have impossible : (none : Option Usize) = some length := by
      simpa only [zero, ite_false] using success
    cases impossible

/-- The source reaches FactorDivision only for the proper, nonconstant GCD
    branch. These widths identify the stored degree fields with the actual
    normalized words passed to the original exact-division call. -/
structure ProperDivideShape (roots : Roots) (buffers : FactorWork) : Prop where
  modulusWidth : buffers.modulus.length = roots.degree.val + 1
  modulusLeading : buffers.modulus[buffers.modulus.length - 1]! ≠ 0#u64
  gcdWidth : roots.gcd_len.val = roots.gcd_degree.val + 1
  gcdPositive : 0 < roots.gcd_degree.val
  proper : roots.gcd_degree.val < roots.degree.val

/-- Degree conservation for the exact result used by the native divide
    theorem's commit admission callback. The pending child has positive degree. -/
def ActualNativeDivideDegree : Prop :=
  ∀ (roots : Roots) (buffers : FactorWork)
    (ready : NativeDivideReady roots buffers) (shape : ProperDivideShape roots buffers)
    (length : Usize), (nativeCall roots buffers).1 = some length →
    let quotient := (nativeCall roots buffers).2.1
    0 < length.val - 1 ∧ length.val ≤ quotient.length ∧
    (prefixSlice quotient length.val)[length.val - 1]! ≠ 0#u64 ∧
    roots.gcd_degree.val + (length.val - 1) = roots.degree.val ∧
    slicePolynomial buffers.modulus =
      slicePolynomial (prefixSlice quotient length.val) * slicePolynomial (prefixSlice buffers.gcd roots.gcd_len.val)

theorem native_call_degree : ActualNativeDivideDegree := by
  intro roots buffers ready shape length success
  let divisor := prefixSlice buffers.gcd roots.gcd_len.val
  let quotient := prefixSlice buffers.work (roots.degree.val + 2)
  let remainder := tail buffers.work (roots.degree.val + 2)
  have divisorLength : divisor.length = roots.gcd_len.val :=
    (prefix_length _ _).trans (Nat.min_eq_left ready.gcdRoom)
  have divisorPositive : 0 < divisor.length := by rw [divisorLength]; exact ready.divisorPositive
  have divisorLeading : divisor[divisor.length - 1]! ≠ 0#u64 := by
    rw [divisorLength]
    exact ready.divisorNonzero
  have modulusPositive : 0 < buffers.modulus.length := by rw [shape.modulusWidth]; omega
  have qRoom : buffers.modulus.length + 1 ≤ quotient.length := by
    unfold quotient
    rw [prefix_length, Nat.min_eq_left ready.workRoom]
    exact ready.quotientRoom
  have remRoom : buffers.modulus.length + 1 ≤ remainder.length := by
    unfold remainder
    rw [tail_length]
    exact ready.remainderRoom
  obtain ⟨_, fits, leading, conservation, decomposition⟩ := exact_division_degree buffers.modulus divisor quotient
    remainder buffers.raw modulusPositive divisorPositive shape.modulusLeading divisorLeading
    qRoom remRoom ready.rawRoom length success
  rw [divisorLength, shape.gcdWidth, shape.modulusWidth] at conservation
  exact ⟨by have proper := shape.proper; omega, fits, leading, by omega, decomposition⟩

#print axioms native_call_degree

end BulksketchBridge.RootDivide
