import BulksketchBridge.AffineMultipleQuotientTrace
import BulksketchBridge.AffineMultipleMinimum

namespace BulksketchBridge.AffineMultiple

open Aeneas.Std Result Polynomial Algebra.Gf64 DenseReducerAlgebra SliceKernels
open DenseCoefficient RebuiltLfsr BmEntry DenseMulConvolutionSpec DenseReducerSquare
open scoped BigOperators

set_option maxRecDepth 4096
set_option maxHeartbeats 2500000

/-- The packed source coefficient representation is the existing affine
polynomial representation, with its first word interpreted as a constant. -/
theorem packed_eq_witness_polynomial (words : Slice U64) (nonempty : 0 < words.length) :
    packedWitness words = witnessPolynomial words[0]! (tail words 1) := by
  have length : words.length = (tail words 1).length + 1 := by rw [tail_length]; omega
  unfold packedWitness weightedValue witnessPolynomial AffineSubspaces.rowPolynomial
  rw [length, Finset.sum_range_succ']
  rw [show columnPower 0 = (1 : Polynomial Field) by simp [columnPower, columnExponent], mul_one, add_comm]
  apply congrArg (fun rest : Polynomial Field => C (toField words[0]!.bv) + rest)
  apply Finset.sum_congr rfl
  intro i _
  rw [tail_word, Nat.add_comm 1 i]
  rfl

/-- The actual original successful native call emits a monic affine
polynomial divisible by the input. The leading degree is exactly the
reported column, independently of the minimality obligation. -/
theorem native_multiple_returned_packed_witness {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice bulksketch.types.RawProduct)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels) (inverse : BmTerminal.NativeInverse kernels)
    (rawMul : RawMulAgrees kernels) (square : SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels)
    (minimum : 4 ≤ polynomial.length) (monic : polynomial[polynomial.length - 1]! = 1#u64)
    (tableLength : table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2))
    (correct : CorrectTable polynomial table (polynomial.length - 1))
    (backend : BackendSquareLaw kernels polynomial table (polynomial.length - 1))
    (layout : Layout (polynomial.length - 1) factors.length work.length affine.length)
    (rawRoom : 2 * (polynomial.length - 1) < raw.length)
    (output : ColumnDone)
    (successful : bulksketch.decode.affine.multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels
      polynomial table factors affine work raw = .ok output) :
    ∃ column : Nat, column ≤ polynomial.length - 1 ∧ output.1.val = column + 1 ∧
      let witness := packedWitness (prefixSlice output.2.2.1 output.1.val)
      witness.Monic ∧ witness.natDegree = columnExponent column ∧ slicePolynomial polynomial ∣ witness := by
  obtain ⟨degree, result, degreeValue, trace, normal⟩ :=
    native_multiple_refines kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
      minimum monic tableLength correct backend layout rawRoom
  obtain ⟨preparedDegree, preparedValue, arena, _⟩ :=
    multiple_prelude_refines RootTrace.nativeSquare kernels polynomial table factors affine work raw layout rawRoom
  have same : preparedDegree = degree := UScalar.eq_of_val_eq (preparedValue.trans degreeValue.symm)
  subst preparedDegree
  have positive : 0 < degree.val := by rw [degreeValue]; have := layout.degree_min; omega
  obtain ⟨rows, image⟩ := prepared_witness_rows degree polynomial table factors affine work raw arena positive
  have full := AffineSplitter.native_full_square kernels rawMul square reduce polynomial table (polynomial.length - 1)
    minimum (by omega) monic tableLength correct backend
  have fullSquare : AffineSplitter.FullSquareLaw RootTrace.nativeSquare kernels
      (preparedShape degree polynomial table affine).polynomial (preparedShape degree polynomial table affine).table
      (preparedShape degree polynomial table affine).degree.val := by
    simpa only [preparedShape, degreeValue] using full
  have rawFits : 2 * degree.val < (preparedState degree.val factors work raw).raw.length := by
    simpa only [preparedState, degreeValue] using rawRoom
  obtain ⟨column, bounded, length, witnessMonic, degreeEq, divides⟩ :=
    successful_trace_witness RootTrace.nativeSquare kernels scale (preparedRestores degree.val factors work)
      (preparedShape degree polynomial table affine) fullSquare ⟨0#usize, degree, false⟩
      (preparedState degree.val factors work raw) result trace rfl rows image rawFits
      output (normal.symm.trans successful)
  exact ⟨column, by simpa only [preparedShape, degreeValue] using bounded,
    length, witnessMonic, degreeEq, divides⟩

/-- Native returned witness in the shared constant-plus-linearized
polynomial representation. -/
def ActualNativeReturnedWitness : Prop :=
  ∀ {K : Type}
    (kernels : bulksketch.backend.contract.BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice bulksketch.types.RawProduct)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels) (inverse : BmTerminal.NativeInverse kernels)
    (rawMul : RawMulAgrees kernels) (square : SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels)
    (minimum : 4 ≤ polynomial.length) (monic : polynomial[polynomial.length - 1]! = 1#u64)
    (tableLength : table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2))
    (correct : CorrectTable polynomial table (polynomial.length - 1))
    (backend : BackendSquareLaw kernels polynomial table (polynomial.length - 1))
    (layout : Layout (polynomial.length - 1) factors.length work.length affine.length)
    (rawRoom : 2 * (polynomial.length - 1) < raw.length)
    (output : ColumnDone)
    (successful : bulksketch.decode.affine.multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels
      polynomial table factors affine work raw = .ok output),
    ∃ column : Nat, column ≤ polynomial.length - 1 ∧ output.1.val = column + 1 ∧
      let words := prefixSlice output.2.2.1 output.1.val
      let witness := witnessPolynomial words[0]! (tail words 1)
      witness.Monic ∧ witness.natDegree = columnExponent column ∧ slicePolynomial polynomial ∣ witness

theorem native_multiple_returned_witness : ActualNativeReturnedWitness := by
  intro K kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
    minimum monic tableLength correct backend layout rawRoom output successful
  obtain ⟨column, bounded, length, leading, degree, divides⟩ :=
    native_multiple_returned_packed_witness kernels polynomial table factors affine work raw scale mul inverse
      rawMul square reduce minimum monic tableLength correct backend layout rawRoom output successful
  let words := prefixSlice output.2.2.1 output.1.val
  have nonempty : 0 < words.length := by
    by_contra empty
    have zero : words.length = 0 := by omega
    have vanished : packedWitness words = 0 := by simp only [packedWitness, weightedValue, zero, Finset.range_zero, Finset.sum_empty]
    exact leading.ne_zero vanished
  have converted := packed_eq_witness_polynomial words nonempty
  exact ⟨column, bounded, length, converted ▸ leading, converted ▸ degree, converted ▸ divides⟩

end BulksketchBridge.AffineMultiple
