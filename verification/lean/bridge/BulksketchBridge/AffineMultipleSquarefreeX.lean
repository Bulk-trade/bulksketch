import BulksketchBridge.AffineMultipleLeastTrace

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Result Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open DenseCoefficient RebuiltLfsr BmEntry DenseMulConvolutionSpec DenseReducerSquare
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem packed_positive_width (modulus words : Slice U64)
    (positive : 0 < (slicePolynomial modulus).natDegree)
    (monic : (packedWitness words).Monic) (divides : slicePolynomial modulus ∣ packedWitness words) :
    1 < words.length := by
  by_contra short
  have short : words.length ≤ 1 := Nat.le_of_not_gt short
  have tooSmall : (packedWitness words).natDegree ≤ 0 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro exponent higher
    simp only [packedWitness, weightedValue, columnPower, C_mul_X_pow_eq_monomial, finsetSum_coeff]
    apply Finset.sum_eq_zero
    intro index member
    have first : index = 0 := by have := Finset.mem_range.mp member; omega
    subst index
    rw [coeff_monomial, show columnExponent 0 = 0 from rfl, ite_eq_right (Nat.ne_of_lt higher)]
  have large := natDegree_le_of_dvd divides monic.ne_zero
  omega

/-- A least packed affine witness for a positive squarefree modulus has
a nonzero X coefficient. Its square root would otherwise be a smaller
packed witness with the same divisibility. -/
theorem packed_squarefree_least_nonzero_X (modulus words : Slice U64)
    (positive : 0 < (slicePolynomial modulus).natDegree) (squarefree : Squarefree (slicePolynomial modulus))
    (monic : (packedWitness words).Monic) (divides : slicePolynomial modulus ∣ packedWitness words)
    (least : ∀ other : Slice U64, packedWitness other ≠ 0 → slicePolynomial modulus ∣ packedWitness other →
      (packedWitness words).natDegree ≤ (packedWitness other).natDegree) :
    1 < words.length ∧ words[1]! ≠ 0#u64 := by
  have width := packed_positive_width modulus words positive monic divides
  refine ⟨width, ?_⟩
  intro zero
  let linear := tail words 1
  have linearLength : linear.length = words.length - 1 := tail_length words 1
  have linearNonempty : 0 < linear.length := by rw [linearLength]; omega
  have zeroX : linear[0]! = 0#u64 := by
    change (tail words 1)[0]! = _
    rw [tail_word, Nat.add_zero, zero]
  let rootLinear := Slice.from ((linear.val.drop 1).map squareRootWord) (by
    rw [List.length_map]
    exact (List.drop_length_is_le _ _).trans linear.length_ineq)
  have rootLen : rootLinear.length = linear.length - 1 := by
    simp only [rootLinear, Slice.length, Slice.from_val, List.length_map, List.length_drop]
  have packRoom : rootLinear.val.length + 1 ≤ Usize.max := by
    change rootLinear.length + 1 ≤ Usize.max
    rw [rootLen, linearLength]
    have bound : words.length ≤ Usize.max := words.length_ineq
    omega
  let rootWords := Slice.from (squareRootWord words[0]! :: rootLinear.val) (by
    rw [List.length_cons]
    exact packRoom)
  have rootNonempty : 0 < rootWords.length := by
    simp only [rootWords, Slice.length, Slice.from_val, List.length_cons, Nat.zero_lt_succ]
  have rootConstant : rootWords[0]! = squareRootWord words[0]! := by
    simp only [rootWords, Slice.getElem!_Nat_eq, Slice.from_val, List.getElem!_cons_zero]
  have rootTail : tail rootWords 1 = rootLinear := by
    apply Slice.ext
    simp only [tail, rootWords, Slice.from_val, List.drop_succ_cons, List.drop_zero]
  have squared : packedWitness rootWords ^ 2 = packedWitness words := by
    rw [packed_eq_witness_polynomial rootWords rootNonempty, rootConstant, rootTail,
      packed_eq_witness_polynomial words (by omega)]
    exact witness_square_root words[0]! linear linearNonempty zeroX
  have rootNZ : packedWitness rootWords ≠ 0 := by
    intro rootZero
    rw [rootZero, zero_pow (by decide)] at squared
    exact monic.ne_zero squared.symm
  have rootDivides : slicePolynomial modulus ∣ packedWitness rootWords :=
    (squarefree.dvd_pow_iff_dvd (by decide : 2 ≠ 0)).mp (squared.symm ▸ divides)
  have rootPositive : 0 < (packedWitness rootWords).natDegree :=
    positive.trans_le (natDegree_le_of_dvd rootDivides rootNZ)
  have minimal := least rootWords rootNZ rootDivides
  rw [← squared, natDegree_pow] at minimal
  omega

/-- The exact original native affine multiple keeps a nonzero X
coefficient for every admitted squarefree input and successful return. -/
def ActualNativeSquarefreeNonzeroX : Prop :=
  ∀ {K : Type} (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice bulksketch.types.RawProduct),
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    4 ≤ polynomial.length → polynomial[polynomial.length - 1]! = 1#u64 →
    table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2) →
    CorrectTable polynomial table (polynomial.length - 1) →
    BackendSquareLaw kernels polynomial table (polynomial.length - 1) →
    Layout (polynomial.length - 1) factors.length work.length affine.length →
    2 * (polynomial.length - 1) < raw.length →
    Squarefree (slicePolynomial polynomial) →
    ∀ output : ColumnDone,
    bulksketch.decode.affine.multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels
      polynomial table factors affine work raw = .ok output →
    output.2.2.1[1]! ≠ 0#u64

theorem native_multiple_squarefree_nonzero_X : ActualNativeSquarefreeNonzeroX := by
  intro K kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
    minimum monic tableLength correct backend layout rawRoom squarefree output successful
  obtain ⟨leading, divides, least⟩ :=
    native_multiple_returned_packed_least kernels polynomial table factors affine work raw scale mul inverse
      rawMul square reduce minimum monic tableLength correct backend layout rawRoom output successful
  have atDegree : (slicePolynomial polynomial).coeff (polynomial.length - 1) = 1 := by
    rw [slicePolynomial_coeff, ite_eq_left (by omega), monic]
    exact toField_one
  have degreeLower : polynomial.length - 1 ≤ (slicePolynomial polynomial).natDegree :=
    le_natDegree_of_ne_zero (by rw [atDegree]; exact one_ne_zero)
  have positive : 0 < (slicePolynomial polynomial).natDegree := by omega
  obtain ⟨width, nonzero⟩ := packed_squarefree_least_nonzero_X polynomial (prefixSlice output.2.2.1 output.1.val)
    positive squarefree leading divides least
  have fits : 1 < output.1.val := by
    rw [prefix_length] at width
    exact width.trans_le (Nat.min_le_left ..)
  rw [prefix_word _ _ _ fits] at nonzero
  exact nonzero

end BulksketchBridge.AffineMultiple
