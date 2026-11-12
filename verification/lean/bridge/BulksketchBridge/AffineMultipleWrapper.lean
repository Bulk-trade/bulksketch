import BulksketchBridge.AffineMultipleLoop
import BulksketchBridge.NativeRootTrace

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std Result
open bulksketch.backend.contract bulksketch.decode.affine bulksketch.types
open DenseCoefficient RebuiltLfsr BmEntry

set_option maxRecDepth 4096
set_option maxHeartbeats 1500000

def preparedShape (degree : Usize) (polynomial table affine : Slice U64) : ColumnShape :=
  ⟨degree, Slice.len polynomial, polynomial, table, affine⟩

def preparedRestores (degree : Nat) (factors work : Slice U64) : ColumnRestores :=
  ⟨splitBack factors (degree * degree), restorePrefix (tail factors (degree * degree)),
    splitBack work degree, splitBack (tail work degree) degree, restorePrefix (tail (tail work degree) degree)⟩

def preparedState (degree : Nat) (factors work : Slice U64) (raw : Slice RawProduct) : ColumnState :=
  ⟨raw, zeroWords (prefixSlice factors (degree * degree)),
    zeroWords (prefixSlice (tail factors (degree * degree)) (degree * (degree + 1))),
    (zeroWords (prefixSlice work degree)).setAtNat 0 1#u64,
    prefixSlice (tail work degree) degree, prefixSlice (tail (tail work degree) degree) (degree + 1)⟩

/-- The original wrapper initializes its exact two matrix windows and
three work windows before invoking the generated column loop. -/
theorem multiple_prelude_refines {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice RawProduct)
    (layout : Layout (polynomial.length - 1) factors.length work.length affine.length)
    (rawRoom : 2 * (polynomial.length - 1) < raw.length) :
    ∃ degree : Usize,
      degree.val = polynomial.length - 1 ∧
      ColumnArena (preparedShape degree polynomial table affine)
        (preparedState degree.val factors work raw) ∧
      multiple square RootSetup.gf64Dictionary kernels polynomial table factors affine work raw =
        columnLoop square kernels (preparedRestores degree.val factors work)
          (preparedShape degree polynomial table affine) ⟨0#usize, degree, false⟩
          (preparedState degree.val factors work raw) := by
  have minimum := layout.degree_min
  obtain ⟨degree, subtracted, added, degreeValue⟩ := degree_width_normal polynomial (by omega)
  have widthValue : polynomial.len.val = degree.val + 1 := by rw [Slice.len_val, degreeValue]; omega
  have factorRoom := layout.factor_room
  rw [← degreeValue] at factorRoom
  obtain ⟨rows, witnesses, rowsNormal, witnessesNormal, rowsValue, witnessesValue⟩ :=
    allocation_products degree polynomial.len factors widthValue factorRoom
  obtain ⟨factorRows, factorWitnesses⟩ := factor_layout layout
  obtain ⟨residueRoom, vectorRoom, workWitnessRoom⟩ := work_layout layout
  rw [← degreeValue] at factorRows factorWitnesses residueRoom vectorRoom workWitnessRoom
  have factorSplit := split_refines factors rows (by rwa [rowsValue])
  have factorCut := prefix_normal (tail factors rows.val) witnesses (by
    rw [tail_length, rowsValue, witnessesValue]
    exact factorWitnesses)
  have workSplit := split_refines work degree residueRoom
  have vectorSplit := split_refines (tail work degree.val) degree (by rwa [tail_length])
  have witnessCut := prefix_normal (tail (tail work degree.val) degree.val) polynomial.len (by
    rw [tail_length, tail_length, widthValue]
    exact workWitnessRoom)
  have initResidue := Reconstruction.update_normal (zeroWords (prefixSlice work degree.val))
    0#usize 1#u64 (by
      rw [zero_length, prefix_length, Nat.min_eq_left residueRoom, degreeValue]
      change 0 < polynomial.length - 1
      omega)
  have initialArena : ColumnArena (preparedShape degree polynomial table affine)
      (preparedState degree.val factors work raw) := by
    unfold ColumnArena preparedShape preparedState
    dsimp only
    refine ⟨⟨widthValue, by simp, ?_, ?_, ?_, ?_⟩, ?_, ?_, by rwa [degreeValue]⟩
    · simp only [zero_length, prefix_length, Nat.min_eq_left factorRows, Nat.le_refl]
    · simp only [zero_length, prefix_length, tail_length, Nat.min_eq_left factorWitnesses, widthValue, Nat.le_refl]
    · simp only [prefix_length, tail_length, Nat.min_eq_left vectorRoom]
    · simp only [prefix_length, tail_length, Nat.min_eq_left workWitnessRoom, widthValue]
    · simp only [Slice.setAtNat_length, zero_length, prefix_length, Nat.min_eq_left residueRoom]
    · rw [degreeValue]
      exact layout.affine_room
  refine ⟨degree, degreeValue, initialArena, ?_⟩
  unfold multiple columnLoop preparedRestores preparedShape preparedState
  simp only [subtracted, added, rowsNormal, bind_ok, factorSplit]
  dsimp! only
  simp only [witnessesNormal, bind_ok, Slice.index_mut_SliceIndexRangeToUsizeSliceInst, factorCut]
  dsimp! only
  simp only [fill_zero, bind_ok, workSplit]
  dsimp! only
  simp only [vectorSplit, bind_ok]
  dsimp! only
  simp only [witnessCut, bind_ok, initResidue, core.ops.range.RangeInclusive.new]
  dsimp! only
  simp only [rowsValue, witnessesValue, widthValue]
  rfl

/-- Exact original affine multiple execution under the admitted arena and
intermediate modular-square contracts. The finite trace retains the panic
case of the generated exhausted column iterator. -/
theorem multiple_refines {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (scaleLaw : TimesXMod.ExactScaleXor kernels) (mulLaw : DenseDivRem.MulWordLaw kernels)
    (inverseLaw : BmTerminal.NativeInverse kernels)
    (polynomial table factors affine work : Slice U64) (raw : Slice RawProduct)
    (layout : Layout (polynomial.length - 1) factors.length work.length affine.length)
    (rawRoom : 2 * (polynomial.length - 1) < raw.length)
    (squareLaw : ∀ (degree : Usize), degree.val = polynomial.length - 1 →
      ∀ (state : ColumnState) (column : Usize), ColumnArena (preparedShape degree polynomial table affine) state →
      column.val ≤ degree.val → columnSquareReady square kernels (preparedShape degree polynomial table affine) state column) :
    ∃ (degree : Usize) (result : Result ColumnDone),
      degree.val = polynomial.length - 1 ∧
      ColumnTrace square kernels (preparedRestores degree.val factors work)
        (preparedShape degree polynomial table affine) ⟨0#usize, degree, false⟩
        (preparedState degree.val factors work raw) result ∧
      multiple square RootSetup.gf64Dictionary kernels polynomial table factors affine work raw = result := by
  obtain ⟨degree, degreeValue, arena, prelude⟩ :=
    multiple_prelude_refines square kernels polynomial table factors affine work raw layout rawRoom
  have minimum : 2 ≤ degree.val := by rw [degreeValue]; exact layout.degree_min
  obtain ⟨result, trace⟩ := column_trace_exists square kernels scaleLaw mulLaw inverseLaw
    (preparedRestores degree.val factors work) (preparedShape degree polynomial table affine)
    minimum (squareLaw degree degreeValue) ⟨0#usize, degree, false⟩ (preparedState degree.val factors work raw) rfl arena
  exact ⟨degree, result, degreeValue, trace, prelude.trans
    (column_loop_refines_trace square kernels scaleLaw mulLaw inverseLaw _ _ _ _ result trace)⟩

open DenseMulConvolutionSpec DenseReducerAlgebra DenseReducerSquare

/-- Original affine multiple execution with the original Dense square call.
The generated operational theorem uses the admitted fixed polynomial/table
and backend contracts. The algebraic minimum is a separate property. -/
def ActualNativeMultiple : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice RawProduct),
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels → BmTerminal.NativeInverse kernels →
    RawMulAgrees kernels → SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    4 ≤ polynomial.length → polynomial[polynomial.length - 1]! = 1#u64 →
    table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2) →
    CorrectTable polynomial table (polynomial.length - 1) →
    BackendSquareLaw kernels polynomial table (polynomial.length - 1) →
    Layout (polynomial.length - 1) factors.length work.length affine.length →
    2 * (polynomial.length - 1) < raw.length →
    ∃ (degree : Usize) (result : Result ColumnDone),
      degree.val = polynomial.length - 1 ∧
      ColumnTrace RootTrace.nativeSquare kernels (preparedRestores degree.val factors work)
        (preparedShape degree polynomial table affine) ⟨0#usize, degree, false⟩
        (preparedState degree.val factors work raw) result ∧
      multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels polynomial table factors affine work raw = result

theorem native_multiple_refines : ActualNativeMultiple := by
  intro K kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
    minimum monic tableLen tableCorrect backend layout rawRoom
  apply multiple_refines RootTrace.nativeSquare kernels scale mul inverse polynomial table factors affine work raw layout rawRoom
  intro degree degreeValue state column arena _ _ _ vector vectorLength
  obtain ⟨_, residueLength, _, rawLength⟩ := arena
  have residueRoom : state.residue.length ≤ polynomial.length - 1 := by
    change state.residue.length = degree.val at residueLength
    rw [residueLength, degreeValue]
  have vectorRoom : polynomial.length - 1 ≤ vector.length := by
    change vector.length = degree.val at vectorLength
    rw [vectorLength, degreeValue]
  have scratchRoom : 2 * (polynomial.length - 1) < state.raw.length := by
    change 2 * degree.val < state.raw.length at rawLength
    rwa [degreeValue] at rawLength
  obtain ⟨size, squared, scratch, normal, _, squareLength, scratchLength, _⟩ :=
    native_modular_square kernels rawMul square reduce polynomial table (polynomial.length - 1)
      minimum (by omega) monic tableLen tableCorrect backend state.residue vector state.raw
      residueRoom vectorRoom scratchRoom
  exact ⟨size, squared, scratch, normal, squareLength.trans vectorLength, scratchLength⟩

end BulksketchBridge.AffineMultiple
