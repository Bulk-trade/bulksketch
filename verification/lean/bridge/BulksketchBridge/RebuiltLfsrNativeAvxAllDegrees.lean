import BulksketchBridge.AvxRebuiltSeed
import BulksketchBridge.RebuiltLfsrAvx
import BulksketchBridge.AvxScalarDelegates

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime
open Algebra.Gf64 Reconciliation DenseCoefficient
open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear odd_recurrence_matches insert_nonzero)

set_option maxRecDepth 4096

/-- The exact GF64 rebuilt verifier uses the original AVX seed for every
admitted degree. Its seed always routes to the checked original tile or
the empty branch, so the remaining insertion leaves need no contracts. -/
def ActualRebuiltLfsrNativeAvxAllDegrees : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
      (one18 one32 : Single) (single : SingleCapacity) (sparse : Batch)
      {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    kernels.multiply_linear = multiply_linear load store portable avxField →
    kernels.odd_recurrence_matches = odd_recurrence_matches load portable avxField →
    kernels.insert_nonzero =
      insert_nonzero one18 one32 single sparse (bulksketch.backend.x86_vpclmul512.insert_tile load) avxField →
    kernels.ArithmeticInst.square =
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.square avxField →
    ∀ (roots odd coefficients expected : Slice U64),
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr avxField kernels roots odd coefficients expected =
          .ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_native_avx_all_degrees : ActualRebuiltLfsrNativeAvxAllDegrees := by
  intro load store loadLaw storeLaw portable one18 one32 single sparse K kernels
    linearEq recurrenceEq insertEq squareEq roots odd coefficients expected unique nonzero coefficientRoom seedRoom
  let shape := prefixSlice expected (min roots.length odd.length)
  have shapeLen : shape.length = min roots.length odd.length := by
    change (prefixSlice expected (min roots.length odd.length)).length = _
    rw [RebuiltLfsr.prefix_length, Nat.min_eq_left seedRoom]
  have fits : shape.length ≤ roots.length := by rw [shapeLen]; exact Nat.min_le_left ..
  obtain ⟨seed, seedNormal, length, values⟩ :=
    AvxRebuiltSeed.native_avx_rebuilt_seed load loadLaw one18 one32 single sparse shape roots fits unique
  have seedLen : seed.length = min roots.length odd.length := length.trans shapeLen
  have supplied : kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots = .ok seed := by
    rw [insertEq, seedLen]
    exact seedNormal
  exact rebuilt_lfsr_avx load store loadLaw storeLaw portable kernels linearEq recurrenceEq
    (AvxScalarDelegates.rebuilt_square_law kernels squareEq) roots odd coefficients expected seed
    unique nonzero coefficientRoom seedRoom seedLen supplied values

#print axioms rebuilt_lfsr_native_avx_all_degrees

end BulksketchBridge.RebuiltLfsr
