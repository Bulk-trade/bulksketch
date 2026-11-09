import BulksketchBridge.NativeRootRun
import BulksketchBridge.RootAffinePreparation
import BulksketchBridge.AffineMultipleNoExhaustion
import BulksketchBridge.AffineSolveMap
import BulksketchBridge.AffineMultipleNativeWitness
import BulksketchBridge.AffineMultipleSquarefreeX

namespace BulksketchBridge.RootAffinePreparation

open Aeneas Aeneas.Std DenseCoefficient RebuiltLfsr BmEntry
open DenseReducerAlgebra DenseReducerSquare SliceKernels Polynomial
open bulksketch.decode.roots bulksketch.decode.scratch bulksketch.backend.contract bulksketch.types

/-- Bounds for the original paid preparation stage before running either
    affine algorithm. Neither callee's return value is an admission premise. -/
structure NativeArena (kernels : BulkKernels K bulksketch.field.Gf64) (roots : Roots) (workspace : RowWorkspace) : Prop where
  degreeMin : 3 ≤ roots.degree.val
  degreeMax : roots.degree.val ≤ 64
  polynomialRoom : roots.degree.val < workspace.polynomials.length
  tableRoom : RootSetup.tableCount roots.degree.val ≤ workspace.square_table.length
  bmRoom : roots.degree.val + 1 ≤ workspace.bm.length
  matrixRoom : AffineMultiple.Layout roots.degree.val workspace.factors.length
    (workspace.bm.length - (roots.degree.val + 1)) (roots.degree.val + 1)
  pendingRoom : roots.stride.val * roots.stride.val ≤ workspace.factors.length
  rawRoom : 2 * roots.degree.val < workspace.raw.length
  monic : workspace.polynomials[roots.degree.val]! = 1#u64
  tableCorrect : CorrectTable (prefixSlice workspace.polynomials (roots.degree.val + 1))
    (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)) roots.degree.val
  backend : BackendSquareLaw kernels (prefixSlice workspace.polynomials (roots.degree.val + 1))
    (prefixSlice workspace.square_table (RootSetup.tableCount roots.degree.val)) roots.degree.val

theorem native_multiple_from_arena {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (arena : NativeArena kernels roots workspace)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels)
    (inverse : BmTerminal.NativeInverse kernels) (rawMul : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (square : SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels) :
    ∃ size factors coefficients work raw,
      multipleInput RootRun.nativeCalls.preparation kernels roots workspace =
        .ok (size, factors, coefficients, work, raw) ∧
      0 < size.val ∧ size.val ≤ roots.degree.val + 1 ∧
      factors.length = workspace.factors.length ∧ coefficients.length = roots.degree.val + 1 ∧
      let words := prefixSlice coefficients size.val
      let witness := AffineMultiple.witnessPolynomial words[0]! (tail words 1)
      let factor := slicePolynomial (prefixSlice workspace.polynomials (roots.degree.val + 1))
      witness.Monic ∧ factor ∣ witness ∧ (Squarefree factor → coefficients[(1 : Nat)]! ≠ 0#u64) := by
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
  have minimum : 4 ≤ polynomial.length := by have := arena.degreeMin; omega
  have monic : polynomial[polynomial.length - 1]! = 1#u64 := by
    rw [degreeEq]
    simp only [polynomial, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
      List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt (Nat.lt_succ_self roots.degree.val)]
    simpa only [Slice.getElem!_Nat_eq, List.getElem!_eq_getElem?_getD] using arena.monic
  obtain ⟨⟨size, factors, coefficients, work, raw⟩, normal, positive, bounded, factorLen, coeffLen, _⟩ :=
    AffineMultiple.native_multiple_returns kernels polynomial table workspace.factors affine scratch workspace.raw
      scale mul inverse rawMul square reduce minimum monic
      (by rw [tableLen, degreeEq, RootSetup.tableCount]) (by rw [degreeEq]; exact arena.tableCorrect)
      (by rw [degreeEq]; exact arena.backend) (by rw [degreeEq, scratchLen, affineLen]; exact arena.matrixRoom)
      (by rw [degreeEq]; exact arena.rawRoom)
  change 0 < size.val at positive
  change size.val ≤ polynomial.length at bounded
  change factors.length = workspace.factors.length at factorLen
  change coefficients.length = affine.length at coeffLen
  obtain ⟨_, _, _, witnessMonic, _, divides⟩ :=
    AffineMultiple.native_multiple_returned_witness kernels polynomial table workspace.factors affine scratch
      workspace.raw scale mul inverse rawMul square reduce minimum monic
      (by rw [tableLen, degreeEq, RootSetup.tableCount]) (by rw [degreeEq]; exact arena.tableCorrect)
      (by rw [degreeEq]; exact arena.backend) (by rw [degreeEq, scratchLen, affineLen]; exact arena.matrixRoom)
      (by rw [degreeEq]; exact arena.rawRoom) (size, factors, coefficients, work, raw) normal
  refine ⟨size, factors, coefficients, work, raw, normal, positive, by rwa [polyLen] at bounded,
    factorLen, coeffLen.trans affineLen, witnessMonic, divides, ?_⟩
  intro simple
  exact AffineMultiple.native_multiple_squarefree_nonzero_X kernels polynomial table workspace.factors affine scratch
    workspace.raw scale mul inverse rawMul square reduce minimum monic
    (by rw [tableLen, degreeEq, RootSetup.tableCount]) (by rw [degreeEq]; exact arena.tableCorrect)
    (by rw [degreeEq]; exact arena.backend) (by rw [degreeEq, scratchLen, affineLen]; exact arena.matrixRoom)
    (by rw [degreeEq]; exact arena.rawRoom) simple (size, factors, coefficients, work, raw) normal

theorem native_preparation_ready {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (arena : NativeArena kernels roots workspace)
    (scale : TimesXMod.ExactScaleXor kernels) (mul : DenseDivRem.MulWordLaw kernels)
    (inverse : BmTerminal.NativeInverse kernels) (rawMul : DenseMulConvolutionSpec.RawMulAgrees kernels)
    (square : SquareAgrees kernels) (reduce : DenseMul.reduceAgrees kernels) :
    Ready RootRun.nativeCalls.preparation kernels roots workspace := by
  obtain ⟨size, factors, coefficients, work, raw, normal, positive, bounded, factorLen, coeffLen, _⟩ :=
    native_multiple_from_arena kernels roots workspace arena scale mul inverse rawMul square reduce
  refine ⟨arena.polynomialRoom, arena.bmRoom, arena.tableRoom, size, factors, coefficients, work, raw, normal,
    by have := arena.degreeMin; omega, ?_⟩
  intro _
  have coefficientRoom : size.val ≤ coefficients.length := by omega
  refine ⟨coefficientRoom, positive, ?_⟩
  let linear := prefixSlice coefficients size.val
  have len : linear.length = size.val := by
    rw [show linear = prefixSlice coefficients size.val from rfl, prefix_length, Nat.min_eq_left coefficientRoom]
  have prefixBound : linear.length ≤ 65 := by have := arena.degreeMax; omega
  have bits : dictionary.BITS = .ok 64#u32 := by
    change Result.ok bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS = _
    rw [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS]
  obtain ⟨_, _, output, solution, residual, _, _, _, _, rankBound, _, returned⟩ :=
    AffineSolveMap.solve_map_gf64_refines dictionary kernels bits scale linear
      (Array.repeat 64#usize 0#u64) (by rwa [len]) prefixBound
  by_cases zero : residual = 0#u64
  · refine ⟨some (solution, output.rank), output.kernel, ?_, rankBound, ?_⟩
    · simpa only [mapInput, zero, ite_true, linear] using returned
    · rw [factorLen]
      exact arena.pendingRoom
  · exact ⟨none, output.kernel, by simpa only [mapInput, zero, ite_false, linear] using returned, trivial⟩

/-- Direct specialization of the original preparation body. -/
def ActualNativeAffinePreparation : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (roots : Roots) (workspace : RowWorkspace) (meter : WorkMeter),
    NativeArena kernels roots workspace →
    TimesXMod.ExactScaleXor kernels → DenseDivRem.MulWordLaw kernels →
    BmTerminal.NativeInverse kernels → DenseMulConvolutionSpec.RawMulAgrees kernels →
    SquareAgrees kernels → DenseMul.reduceAgrees kernels →
    Roots.prepare_affine RootRun.nativeCalls.preparation dictionary kernels roots workspace meter =
      expected RootRun.nativeCalls.preparation kernels roots workspace meter

theorem native_preparation_refines : ActualNativeAffinePreparation := by
  intro K kernels roots workspace meter arena scale mul inverse rawMul square reduce
  exact prepare_affine_refines RootRun.nativeCalls.preparation kernels roots workspace meter
    (fun _ _ => native_preparation_ready kernels roots workspace arena scale mul inverse rawMul square reduce)

end BulksketchBridge.RootAffinePreparation
