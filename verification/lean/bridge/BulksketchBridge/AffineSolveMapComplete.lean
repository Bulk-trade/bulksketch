import BulksketchBridge.AffineSolveMapKernelSpan

namespace BulksketchBridge.AffineSolveMap

open Aeneas Aeneas.Std Algebra.Gf64 FrobeniusTables AffineSubspaceAlgebra
open bulksketch.backend.contract bulksketch.decode.affine
open AffineSubspaces (prefixDirections)
open DenseCoefficient (prefixSlice)
open RebuiltLfsr (prefix_length)

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

local instance : CharP Field 2 :=
  charP_of_injective_ringHom (algebraMap (ZMod 2) Field).injective 2

theorem field_lift_linear_word (coefficients : Slice U64) (point : Field) :
    fieldLift (linearWord coefficients) point =
      AffineLinearEval.linearValueFrom coefficients ⟨wordFieldEquiv.symm point⟩ 0 :=
  linear_word_field _ _

def NativeFiber (coefficients : Slice U64) (target : U64) (written : Columns) :
    Option (U64 × Usize) → Prop
  | none => ¬ ∃ point : Field, fieldLift (linearWord coefficients) point = value target
  | some (base, rank) =>
      let basis := prefixSlice written.to_slice rank.val
      let directions := prefixDirections basis basis.length
      rank.val ≤ 64 ∧ basis.length = rank.val ∧ AffineEnumerate.IndependentDirections basis ∧
      fieldLift (linearWord coefficients) (value base) = value target ∧
      (∀ point : Field, fieldLift (linearWord coefficients) point = 0 ↔ point ∈ spanWords directions) ∧
      (∀ point : Field, fieldLift (linearWord coefficients) point = value target ↔ point ∈ coset (value base) directions)

/-- The actual original solver returns None exactly for an empty fiber, or a
particular base and an independent kernel basis spanning the entire fiber. -/
def ActualNativeSolveMapFibers : Prop :=
  ∀ {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64),
    field.BITS = .ok 64#u32 → TimesXMod.ExactScaleXor kernels →
    ∀ (affine : Slice U64) (initial : Columns), 0 < affine.length → affine.length ≤ 65 →
    ∃ (coefficients : Slice U64) (answer : Option (U64 × Usize)) (written : Columns),
      coefficients.val = affine.val.drop 1 ∧
      solve_map field kernels affine initial = .ok (answer, written) ∧
      NativeFiber coefficients affine[0]! written answer

theorem native_solve_map_fibers : ActualNativeSolveMapFibers := by
  intro K field kernels bits scale affine initial positive width
  obtain ⟨coefficients, table, output, reduced, final, linear, tableOK, trace,
    pivots, rankBound, reduction, solved⟩ := solve_map_gf64_refines field kernels bits scale affine initial positive width
  let columns := foldColumns coefficients table 0 (Array.repeat 64#usize 0#u64) coefficients.length
  let map := linearWord coefficients
  have mapLinear : XorLinear map := linear_word_additive coefficients
  have coefficientWidth : coefficients.length ≤ 64 := by
    have length : coefficients.length = affine.length - 1 := by
      rw [Slice.length, linear, List.length_drop]
    omega
  have columnValues (i : Nat) (active : i < 64) : map (basisBit i) = columns.to_slice[i]! := by
    apply U64.bv_eq_imp_eq
    apply toField_injective
    change toField (linearWord coefficients (basisBit i)).bv = toField columns.to_slice[i]!.bv
    rw [linear_word_field, Slice.getElem!_Nat_eq, Array.to_slice, Slice.from_val]
    change AffineLinearEval.linearValueFrom coefficients (column 0 i) 0 = toField (entry columns i).bv
    exact (native_columns_linearized coefficients table tableOK coefficientWidth i active).symm
  have complete := elimination_kernel_span trace map mapLinear columnValues (Nat.le_refl _)
    (Nat.zero_le _) (sweep_spans_empty map mapLinear initial)
  refine ⟨coefficients, _, output.kernel, linear, solved, ?_⟩
  by_cases zero : final = 0#u64
  · rw [ite_eq_left zero]
    let basis := prefixSlice output.kernel.to_slice output.rank.val
    have basisLength : basis.length = output.rank.val := by
      change (prefixSlice output.kernel.to_slice output.rank.val).length = _
      rw [prefix_length, Array.length_to_slice, show (64#usize).val = 64 from rfl, Nat.min_eq_left rankBound]
    have directions : prefixDirections basis basis.length = kernelBasis output := by
      rw [basisLength]
      unfold kernelBasis
      apply prefix_directions_congr
      intro i inside
      simp only [basis, prefixSlice, Slice.getElem!_Nat_eq, Slice.from_val,
        List.getElem!_eq_getElem?_getD, List.getElem?_take_of_lt inside]
    have result := congrArg value (reduce_target_graph map mapLinear complete.graph reduction)
    have xorValue (left right : U64) : value (left ^^^ right) = value left + value right :=
      toField_xor _ _
    rw [xorValue, xorValue, zero, mapLinear.1] at result
    have zeroValue : value 0#u64 = 0 := toField_zero
    rw [zeroValue, add_zero, zero_add] at result
    have solvedBase : fieldLift map (value reduced) = value affine[0]! := by
      rw [field_lift_word, result]
    change output.rank.val ≤ 64 ∧ basis.length = output.rank.val ∧ AffineEnumerate.IndependentDirections basis ∧
      fieldLift map (value reduced) = value affine[0]! ∧ _ ∧ _
    rw [directions]
    exact ⟨rankBound, basisLength, kernel_prefix_independent output 64 rankBound complete.triangular,
      solvedBase, complete_kernel complete.kernel,
      fun point => fiber_of_kernel_basis (fieldLift map) (field_lift_add map mapLinear) (kernelBasis output)
        (value reduced) (value affine[0]!) point (complete_kernel complete.kernel) solvedBase⟩
  · rw [ite_eq_right zero]
    exact failed_target_excludes map pivots complete.image reduction zero

/-- The observed native None result is equivalent to an empty mathematical
fiber of the exact input polynomial. -/
theorem native_solve_map_none_iff {K : Type} (field : bulksketch.field.BinaryField bulksketch.field.Gf64)
    (kernels : BulkKernels K bulksketch.field.Gf64)
    (bits : field.BITS = .ok 64#u32) (scale : TimesXMod.ExactScaleXor kernels)
    (affine : Slice U64) (initial written : Columns) (answer : Option (U64 × Usize))
    (positive : 0 < affine.length) (width : affine.length ≤ 65)
    (normal : solve_map field kernels affine initial = .ok (answer, written)) :
    ∃ coefficients : Slice U64, coefficients.val = affine.val.drop 1 ∧
      (answer = none ↔ ¬ ∃ point : Field,
        fieldLift (linearWord coefficients) point = value affine[0]!) := by
  obtain ⟨coefficients, actual, actualWritten, linear, solved, fiber⟩ :=
    native_solve_map_fibers field kernels bits scale affine initial positive width
  have exactResult := Result.ok_injective (solved.symm.trans normal)
  have exactAnswer : actual = answer := congrArg Prod.fst exactResult
  have exactKernel : actualWritten = written := congrArg Prod.snd exactResult
  rw [exactAnswer, exactKernel] at fiber
  refine ⟨coefficients, linear, ?_⟩
  cases answer with
  | none => exact ⟨fun _ => fiber, fun _ => rfl⟩
  | some pair =>
    rcases pair with ⟨base, rank⟩
    obtain ⟨_, _, _, valueBase, _, _⟩ := fiber
    constructor
    · intro impossible
      cases impossible
    · intro empty
      exact (empty ⟨value base, valueBase⟩).elim

#print axioms native_solve_map_fibers
#print axioms native_solve_map_none_iff

end BulksketchBridge.AffineSolveMap
