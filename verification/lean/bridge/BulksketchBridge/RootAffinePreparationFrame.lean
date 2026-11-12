import BulksketchBridge.RootAffineCoset
import BulksketchBridge.RootTraversalFactor
import BulksketchBridge.RootTraversalRankLinks
import BulksketchBridge.RootAffineRetry

namespace BulksketchBridge.AffineMultiple

open Aeneas Aeneas.Std RebuiltLfsr BmEntry DenseCoefficient
open bulksketch.decode.affine
open bulksketch.backend.contract bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem column_trace_raw_width {K : Type} (square : RootTraceRuntime.ModularSquare)
    (kernels : BulkKernels K bulksketch.field.Gf64) (scale : TimesXMod.ExactScaleXor kernels)
    (restores : ColumnRestores) (shape : ColumnShape) (iter : ColumnIter) (state : ColumnState)
    (result : Result ColumnDone) (trace : ColumnTrace square kernels restores shape iter state result)
    (output : ColumnDone) (normal : result = .ok output) :
    output.2.2.2.2.length = state.raw.length := by
  induction trace with
  | exhausted yielded => exact (fail_not_ok normal).elim
  | @dependent iter next state column length yielded ready _ lengthValue =>
    have exactOutput := Result.ok_injective normal
    subst output
    simp only [dependentOutput]
  | @pivot iter next state column advanced result yielded ready _ squareReady stored rest ih =>
    obtain ⟨vector, witness, row, search, _, _, _, residue⟩ := stored
    have rawWidth : advanced.raw.length = state.raw.length := by
      by_cases first : column = 0#usize
      · rw [advancedResidue, ite_eq_left first] at residue
        exact congrArg (fun value => Slice.length value.2.2) (Result.ok_injective residue).symm
      · by_cases last : column = shape.degree
        · rw [advancedResidue, ite_eq_right first, ite_eq_left last] at residue
          exact congrArg (fun value => Slice.length value.2.2) (Result.ok_injective residue).symm
        · let initial := initialWitness column state.witness
          have fitted : PivotLayout shape.degree shape.width column state.rows state.witnesses state.residue initial :=
            ⟨ready.1.widthValue, ready.1.columnRoom, ready.1.rowsRoom, ready.1.witnessesRoom, ready.2.1,
              by simp only [initial, initialWitness, Slice.setAtNat_length, zero_length, ready.1.witnessWidth]⟩
          obtain ⟨actual, _, _, _, model, final, _⟩ :=
            pivot_search_refines kernels scale shape.degree shape.width column state.rows state.witnesses
              state.residue initial ⟨0#usize, shape.degree⟩ fitted rfl
          have vectorEq : actual = vector := by
            unfold searchedColumn at search
            have exactModel : _ = (pivotSearch shape.degree.val column.val state.rows state.witnesses
                shape.degree.val 0 state.residue initial).1 :=
              congrArg Prod.fst model.symm
            rw [search] at exactModel
            exact exactModel
          obtain ⟨size, squared, scratch, squaredCall, _, scratchWidth⟩ :=
            squareReady first last vector (vectorEq ▸ final.vectorWidth)
          rw [advancedResidue, ite_eq_right first, ite_eq_right last, squaredCall, bind_ok] at residue
          exact (congrArg (fun value => Slice.length value.2.2)
            (Result.ok_injective residue)).symm.trans scratchWidth
    exact (ih normal).trans rawWidth

/-- The native affine multiple returns every mutable arena at its
original width, including the raw square scratch. -/
theorem native_multiple_output_widths {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (polynomial table factors affine work : Slice U64) (raw : Slice RawProduct)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels)
    (inverse : BmTerminal.NativeInverse kernels) (rawMul : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (square : DenseReducerSquare.SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels)
    (minimum : 4 ≤ polynomial.length) (monic : polynomial[polynomial.length - 1]! = 1#u64)
    (tableLen : table.length = (polynomial.length - 1) * ((polynomial.length - 1) / 2))
    (correct : DenseReducerAlgebra.CorrectTable polynomial table (polynomial.length - 1))
    (backend : DenseReducerSquare.BackendSquareLaw kernels polynomial table (polynomial.length - 1))
    (layout : Layout (polynomial.length - 1) factors.length work.length affine.length)
    (rawRoom : 2 * (polynomial.length - 1) < raw.length)
    (output : ColumnDone)
    (normal : multiple RootTrace.nativeSquare RootSetup.gf64Dictionary kernels polynomial table factors affine work raw =
      .ok output) :
    output.2.1.length = factors.length ∧ output.2.2.1.length = affine.length ∧
      output.2.2.2.1.length = work.length ∧ output.2.2.2.2.length = raw.length := by
  obtain ⟨returned, computed, _, _, factorsWidth, affineWidth, workWidth⟩ :=
    native_multiple_returns kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
      minimum monic tableLen correct backend layout rawRoom
  have returnedEq := Result.ok_injective (computed.symm.trans normal)
  subst returned
  obtain ⟨degree, result, _, trace, actual⟩ :=
    native_multiple_refines kernels polynomial table factors affine work raw scale mul inverse rawMul square reduce
      minimum monic tableLen correct backend layout rawRoom
  exact ⟨factorsWidth, affineWidth, workWidth, column_trace_raw_width _ kernels scale _ _ _ _ _ trace _ (actual.symm.trans normal)⟩

end BulksketchBridge.AffineMultiple

namespace BulksketchBridge.RootAffinePreparation

open Aeneas Aeneas.Std RebuiltLfsr BmEntry DenseCoefficient
open DenseReducerAlgebra DenseReducerSquare SliceKernels Polynomial
open bulksketch.backend.contract bulksketch.decode.roots bulksketch.decode.scratch bulksketch.types

set_option maxRecDepth 4096
set_option maxHeartbeats 2200000

theorem native_multiple_input_widths {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (arena : NativeArena kernels roots workspace)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels)
    (inverse : BmTerminal.NativeInverse kernels) (rawMul : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (square : SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels)
    (size : Usize) (factors coefficients work : Slice U64) (raw : Slice RawProduct)
    (normal : multipleInput RootRun.nativeCalls.preparation kernels roots workspace =
      .ok (size, factors, coefficients, work, raw)) :
    factors.length = workspace.factors.length ∧ coefficients.length = roots.degree.val + 1 ∧
      work.length = workspace.bm.length - (roots.degree.val + 1) ∧ raw.length = workspace.raw.length := by
  let polynomial := prefixSlice workspace.polynomials (roots.degree.val + 1)
  let table := prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)
  let affine := prefixSlice workspace.bm (roots.degree.val + 1)
  let scratch := tail workspace.bm (roots.degree.val + 1)
  have polyLen : polynomial.length = roots.degree.val + 1 := by
    rw [show polynomial = prefixSlice workspace.polynomials (roots.degree.val + 1) from rfl,
      prefix_length, Nat.min_eq_left (by have := arena.polynomialRoom; omega)]
  have tableLen : table.length = RootSetup.tableCount roots.degree.val := by
    rw [show table = prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val) from rfl,
      prefix_length, Nat.min_eq_left arena.tableRoom]
  have affineLen : affine.length = roots.degree.val + 1 := by
    rw [show affine = prefixSlice workspace.bm (roots.degree.val + 1) from rfl,
      prefix_length, Nat.min_eq_left arena.bmRoom]
  have scratchLen : scratch.length = workspace.bm.length - (roots.degree.val + 1) := tail_length ..
  have degreeEq : polynomial.length - 1 = roots.degree.val := by omega
  have monic : polynomial[polynomial.length - 1]! = 1#u64 := by
    rw [degreeEq]
    simp only [polynomial, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
      List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt (Nat.lt_succ_self roots.degree.val)]
    simpa only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using arena.monic
  obtain ⟨factorWidth, coeffWidth, workWidth, rawWidth⟩ :=
    AffineMultiple.native_multiple_output_widths kernels polynomial table workspace.factors affine scratch
      workspace.raw scale mul inverse rawMul square reduce (by have := arena.degreeMin; omega) monic
      (by rw [tableLen, degreeEq, RootSetup.tableCount]) (by rw [degreeEq]; exact arena.tableCorrect)
      (by rw [degreeEq]; exact arena.backend) (by rw [degreeEq, scratchLen, affineLen]; exact arena.matrixRoom)
      (by rw [degreeEq]; exact arena.rawRoom) (size, factors, coefficients, work, raw) normal
  exact ⟨factorWidth, coeffWidth.trans affineLen, workWidth.trans scratchLen, rawWidth⟩


/-- Successful preparation may rewrite the factor and elimination scratch,
    but it leaves all allocations, the live polynomial, roots and stack intact. -/
theorem native_preparation_frame {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots after : Roots) (workspace written : RowWorkspace) (meter paid : WorkMeter) (stage : Stage)
    (arena : NativeArena kernels roots workspace)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels)
    (inverse : BmTerminal.NativeInverse kernels) (rawMul : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (square : SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels)
    (charged : charge meter (.AffinePreparation roots.degree) = .ok (.Ok (), paid))
    (ran : Roots.prepare_affine RootRun.nativeCalls.preparation dictionary kernels roots workspace meter =
      .ok (.Ok (.Ok stage), after, written, id, paid)) :
    RootRun.workspaceLengths written = RootRun.workspaceLengths workspace ∧
      written.polynomials = workspace.polynomials ∧ written.square_table = workspace.square_table ∧
      written.roots = workspace.roots ∧ written.stack = workspace.stack ∧
      (stage = .AffineEnumeration → bulksketch.decode.affine.enumerate_preferred roots.degree after.affine_rank = .ok true) := by
  obtain ⟨size, factors, coefficients, work, raw, normal, _, _, _, _, _⟩ :=
    native_multiple_from_arena kernels roots workspace arena scale mul inverse rawMul square reduce
  obtain ⟨factorWidth, coeffWidth, workWidth, rawWidth⟩ :=
    native_multiple_input_widths kernels roots workspace arena scale mul inverse rawMul square reduce
      size factors coefficients work raw normal
  have paidModel : StageCharge.chargeResult meter (RootRun.affinePreparationCost roots.degree) = (.Ok (), paid) := by
    have exactCharge := RootRun.roots_charge_returns meter (.AffinePreparation roots.degree)
      (RootRun.affinePreparationCost roots.degree) (RootRun.affine_preparation_cost_refines roots.degree)
    rw [charged] at exactCharge
    exact Result.ok.injEq.mp exactCharge.symm
  rw [native_preparation_refines kernels roots workspace meter arena scale mul inverse rawMul square reduce] at ran
  simp only [expected, paidModel, normal, bind_ok] at ran
  dsimp! only at ran
  have fields (basis : SplitterBasis) (outFactors : Slice U64) (width : outFactors.length = factors.length)
      (eq : written = {workspace with
        bm := splitBack workspace.bm (roots.degree.val + 1) (coefficients, work)
        factors := outFactors
        raw := raw
        basis := basis}) :
      RootRun.workspaceLengths written = RootRun.workspaceLengths workspace ∧
        written.polynomials = workspace.polynomials ∧ written.square_table = workspace.square_table ∧
        written.roots = workspace.roots ∧ written.stack = workspace.stack := by
    subst written
    simp only [RootRun.workspaceLengths, splitBack_length, width, factorWidth, rawWidth, and_self]
  split at ran
  · have frame := Result.ok_injective ran
    cases frame
  · cases mapped : mapInput kernels size coefficients using Result.cases with
    | ret mapping =>
      rcases mapping with ⟨option, directions⟩
      simp only [mapped, bind_ok] at ran
      dsimp! only at ran
      cases option with
      | none =>
        have frame := Result.ok_injective ran
        cases frame
      | some solved =>
        obtain ⟨base, rank⟩ := solved
        dsimp! only at ran
        split at ran
        · have frame := Result.ok_injective ran
          cases frame
        · split at ran
          · have frame := Result.ok_injective ran
            cases frame
          · cases selected : bulksketch.decode.affine.enumerate_preferred roots.degree rank using Result.cases with
            | ret enumerate =>
              simp only [selected, bind_ok] at ran
              cases enumerate
              · simp only [Bool.false_eq_true, ite_false] at ran
                cases subspaces : bulksketch.decode.affine.subspaces dictionary kernels
                  (prefixSlice directions.to_slice rank.val) (tail factors (roots.stride.val * roots.stride.val)) using Result.cases with
                | ret updated =>
                  simp only [subspaces, bind_ok] at ran
                  have frame := Result.ok_injective ran
                  have fieldsEq := fields _ _ (Slice.setSlice!_length ..)
                    (congrArg (fun value : Frame => value.2.2.1) frame).symm
                  refine ⟨fieldsEq.1, fieldsEq.2.1, fieldsEq.2.2.1, fieldsEq.2.2.2.1, fieldsEq.2.2.2.2, ?_⟩
                  intro enum
                  rw [enum] at frame
                  cases congrArg Prod.fst frame
                | vis effect continuation =>
                  simp only [subspaces, bind_vis] at ran
                  exact (vis_not_ok ran).elim
                | div =>
                  simp only [subspaces, bind_div] at ran
                  exact (div_not_ok ran).elim
              · simp only [ite_true] at ran
                have frame := Result.ok_injective ran
                have fieldsEq := fields _ _ rfl (congrArg (fun value : Frame => value.2.2.1) frame).symm
                have rankEq : rank = after.affine_rank :=
                  congrArg (fun value : Frame => value.2.1.affine_rank) frame
                refine ⟨fieldsEq.1, fieldsEq.2.1, fieldsEq.2.2.1, fieldsEq.2.2.2.1, fieldsEq.2.2.2.2, ?_⟩
                intro _
                exact rankEq ▸ selected
            | vis effect continuation =>
              simp only [selected, bind_vis] at ran
              exact (vis_not_ok ran).elim
            | div =>
              simp only [selected, bind_div] at ran
              exact (div_not_ok ran).elim
    | vis effect continuation =>
      simp only [mapped, bind_vis] at ran
      exact (vis_not_ok ran).elim
    | div =>
      simp only [mapped, bind_div] at ran
      exact (div_not_ok ran).elim

end BulksketchBridge.RootAffinePreparation
