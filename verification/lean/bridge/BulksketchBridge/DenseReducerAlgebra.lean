import BulksketchBridge.TimesXMod
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.Polynomial.Expand

namespace BulksketchBridge.DenseReducerAlgebra

open Aeneas.Std Algebra.Gf64 DenseCoefficient SliceKernels TimesXMod Polynomial
open bulksketch.backend.contract
open scoped BigOperators

set_option maxRecDepth 4096

noncomputable abbrev residue (modulus : Slice U64) := AdjoinRoot.mk (slicePolynomial modulus)
noncomputable abbrev residueX (modulus : Slice U64) := AdjoinRoot.root (slicePolynomial modulus)

def firstHigh (degree : Nat) : Nat := (degree + 1) / 2

def tableRow (table : Slice U64) (degree row : Nat) : Slice U64 :=
  ClosedLeaf.region table (row * degree) ((row + 1) * degree)

/-- Dense table rows represent consecutive high even exponents in the
quotient ring. The low coefficients and table share the native degree. -/
structure CorrectTable (modulus table : Slice U64) (degree : Nat) : Prop where
  room : degree * (degree / 2) ≤ table.length
  rowImage : ∀ row < degree / 2,
    residue modulus (slicePolynomial (tableRow table degree row)) = residueX modulus ^ (2 * (firstHigh degree + row))

theorem table_row_length (modulus table : Slice U64) (degree row : Nat)
    (valid : CorrectTable modulus table degree) (rowBound : row < degree / 2) :
    (tableRow table degree row).length = degree := by
  have bounded : (row + 1) * degree ≤ table.length :=
    (Nat.mul_le_mul_right degree (by omega : row + 1 ≤ degree / 2)).trans
      (by simpa only [Nat.mul_comm] using valid.room)
  rw [tableRow, ClosedLeaf.region_length _ _ _ bounded, Nat.add_mul]
  omega

theorem monic_low_image (modulus : Slice U64) (degree : Nat)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64) :
    residue modulus (slicePolynomial (prefixSlice modulus degree)) = residueX modulus ^ degree := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  unfold residue residueX
  rw [← AdjoinRoot.mk_X, ← map_pow, AdjoinRoot.mk_eq_mk, sub_eq_add_neg, CharTwo.neg_eq]
  refine ⟨1, ?_⟩
  rw [mul_one, monic_words modulus degree shape monic, ← C_mul_X_pow_eq_monomial, map_one, one_mul]

/-- One original native shift multiplies a residue by the image of X. -/
theorem shift_image {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (row modulus : Slice U64)
    (positive : 0 < row.length) (shape : modulus.length = row.length + 1)
    (monic : modulus[row.length]! = 1#u64) :
    ∃ output,
      bulksketch.poly.dense.times_x_mod bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels row modulus =
        .ok output ∧ output.length = row.length ∧
      residue modulus (slicePolynomial output) = residueX modulus * residue modulus (slicePolynomial row) := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  obtain ⟨output, normal, len, represented⟩ :=
    times_x_mod_polynomial kernels arithmetic row modulus positive shape monic
  refine ⟨output, normal, len, ?_⟩
  symm
  unfold residue residueX
  rw [← AdjoinRoot.mk_X, ← map_mul, AdjoinRoot.mk_eq_mk, sub_eq_add_neg, CharTwo.neg_eq]
  exact represented

theorem initial_row_image {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (modulus : Slice U64) (degree : Nat)
    (positive : 0 < degree) (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64) :
    let low := prefixSlice modulus degree
    ∃ row,
      (if degree % 2 = 0 then .ok low else
        bulksketch.poly.dense.times_x_mod bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels low modulus)
        = .ok row ∧ row.length = degree ∧
      residue modulus (slicePolynomial row) = residueX modulus ^ (2 * firstHigh degree) := by
  let low := prefixSlice modulus degree
  have lowLen : low.length = degree := (RebuiltLfsr.prefix_length _ _).trans (Nat.min_eq_left (by omega))
  have initialImage := monic_low_image modulus degree shape monic
  by_cases even : degree % 2 = 0
  · refine ⟨low, by simp only [even, ite_true, low], lowLen, ?_⟩
    rw [initialImage, show 2 * firstHigh degree = degree by unfold firstHigh; omega]
  · obtain ⟨row, shifted, len, image⟩ := shift_image kernels arithmetic low modulus (by omega)
      (by omega) (by rw [lowLen]; exact monic)
    refine ⟨row, by simpa only [even, ite_false] using shifted, len.trans lowLen, ?_⟩
    rw [image, initialImage, ← pow_succ', show 2 * firstHigh degree = degree + 1 by unfold firstHigh; omega]

/-- The two original native calls advance the table by two exponents. -/
theorem next_row_image {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (arithmetic : ExactScaleXor kernels) (row modulus : Slice U64) (exponent : Nat)
    (positive : 0 < row.length) (shape : modulus.length = row.length + 1)
    (monic : modulus[row.length]! = 1#u64)
    (value : residue modulus (slicePolynomial row) = residueX modulus ^ exponent) :
    ∃ intermediate output,
      bulksketch.poly.dense.times_x_mod bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels row modulus =
        .ok intermediate ∧
      bulksketch.poly.dense.times_x_mod bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels intermediate modulus =
        .ok output ∧ output.length = row.length ∧
      residue modulus (slicePolynomial output) = residueX modulus ^ (exponent + 2) := by
  obtain ⟨intermediate, first, firstLen, firstValue⟩ := shift_image kernels arithmetic row modulus positive shape monic
  obtain ⟨output, second, secondLen, secondValue⟩ :=
    shift_image kernels arithmetic intermediate modulus (by omega) (by omega) (by rwa [firstLen])
  refine ⟨intermediate, output, first, second, secondLen.trans firstLen, ?_⟩
  rw [secondValue, firstValue, value, ← pow_succ', ← pow_succ']

noncomputable def reduceSquare (input table : Slice U64) (degree : Nat) : Polynomial Field :=
  ∑ i ∈ Finset.range input.length, C ((slicePolynomial input).coeff i ^ 2) *
    (if i < firstHigh degree then X ^ (2 * i) else
      slicePolynomial (tableRow table degree (i - firstHigh degree)))

private theorem slice_expansion (input : Slice U64) :
    slicePolynomial input = ∑ i ∈ Finset.range input.length, monomial i ((slicePolynomial input).coeff i) := by
  classical
  ext j
  rw [finsetSum_coeff]
  by_cases active : j < input.length
  · rw [Finset.sum_eq_single j, coeff_monomial, ite_eq_left rfl]
    · intro i _ other
      rw [coeff_monomial, ite_eq_right other]
    · intro absent
      exact (absent (Finset.mem_range.mpr active)).elim
  · rw [slicePolynomial_coeff, ite_eq_right active]
    symm
    apply Finset.sum_eq_zero
    intro i member
    have other : i ≠ j := by
      have := Finset.mem_range.mp member
      omega
    rw [coeff_monomial, ite_eq_right other]

private theorem square_expansion (input : Slice U64) :
    slicePolynomial input ^ 2 =
      ∑ i ∈ Finset.range input.length, C ((slicePolynomial input).coeff i ^ 2) * X ^ (2 * i) := by
  let _ : CharP Field 2 := charP_of_injective_algebraMap' (ZMod 2) 2
  rw [← map_frobenius_expand 2]
  conv_lhs => rw [slice_expansion input]
  simp only [map_sum, expand_monomial, Polynomial.map_sum, map_monomial, frobenius_def]
  apply Finset.sum_congr rfl
  intro i _
  rw [← C_mul_X_pow_eq_monomial, Nat.mul_comm i 2]

/-- The fallback square's low monomials and high table contributions
represent the square of the input in the native monic quotient. -/
theorem square_image (input modulus table : Slice U64) (degree : Nat)
    (inputBound : input.length ≤ degree) (valid : CorrectTable modulus table degree) :
    residue modulus (reduceSquare input table degree) = (residue modulus (slicePolynomial input)) ^ 2 := by
  rw [← map_pow, square_expansion, reduceSquare, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i member
  simp only [map_mul]
  congr 1
  by_cases low : i < firstHigh degree
  · rw [ite_eq_left low]
  · have admitted := Finset.mem_range.mp member
    rw [ite_eq_right low, map_pow, AdjoinRoot.mk_X,
      valid.rowImage (i - firstHigh degree) (by unfold firstHigh at *; omega)]
    rw [show firstHigh degree + (i - firstHigh degree) = i by omega]

theorem modulus_monic (modulus : Slice U64) (degree : Nat)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64) :
    (slicePolynomial modulus).Monic ∧ (slicePolynomial modulus).degree = degree := by
  have leading : (slicePolynomial modulus).coeff degree = 1 := by
    rw [slicePolynomial_coeff, ite_eq_left (by omega), monic]
    exact toField_one
  have upper : (slicePolynomial modulus).natDegree ≤ degree := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i beyond
    rw [slicePolynomial_coeff, ite_eq_right (by omega)]
  have nonzero : (slicePolynomial modulus).coeff degree ≠ 0 := by rw [leading]; exact one_ne_zero
  have monicPoly := monic_of_natDegree_le_of_coeff_eq_one degree upper leading
  refine ⟨monicPoly, ?_⟩
  rw [degree_eq_natDegree monicPoly.ne_zero, natDegree_eq_of_le_of_coeff_ne_zero upper nonzero]

theorem square_degree (input modulus table : Slice U64) (degree : Nat)
    (inputBound : input.length ≤ degree) (valid : CorrectTable modulus table degree) :
    (reduceSquare input table degree).degree < degree := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro n above
  rw [reduceSquare, finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro i member
  rw [coeff_C_mul]
  by_cases low : i < firstHigh degree
  · have other : n ≠ 2 * i := by unfold firstHigh at low; omega
    rw [ite_eq_left low, coeff_X_pow, ite_eq_right other, mul_zero]
  · have active := Finset.mem_range.mp member
    have rowBound : i - firstHigh degree < degree / 2 := by unfold firstHigh at *; omega
    have zero : (slicePolynomial (tableRow table degree (i - firstHigh degree))).coeff n = 0 := by
      rw [slicePolynomial_coeff, table_row_length modulus table degree _ valid rowBound, ite_eq_right (by omega)]
    rw [ite_eq_right low, zero, mul_zero]

/-- The quotient-ring equation and native degree bound characterize the
exact monic remainder of the square. -/
theorem square_remainder (input modulus table : Slice U64) (degree : Nat)
    (shape : modulus.length = degree + 1) (monic : modulus[degree]! = 1#u64)
    (inputBound : input.length ≤ degree) (valid : CorrectTable modulus table degree) :
    reduceSquare input table degree = slicePolynomial input ^ 2 %ₘ slicePolynomial modulus := by
  obtain ⟨monicPoly, modulusDegree⟩ := modulus_monic modulus degree shape monic
  have small : (reduceSquare input table degree).degree < (slicePolynomial modulus).degree := by
    rw [modulusDegree]
    exact square_degree input modulus table degree inputBound valid
  have image := square_image input modulus table degree inputBound valid
  rw [← map_pow] at image
  have result := congrArg (AdjoinRoot.modByMonicHom monicPoly) image
  rw [AdjoinRoot.modByMonicHom_mk, AdjoinRoot.modByMonicHom_mk, (modByMonic_eq_self_iff monicPoly).mpr small] at result
  exact result

end BulksketchBridge.DenseReducerAlgebra
