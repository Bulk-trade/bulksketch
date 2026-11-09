import BulksketchBridge.RebuiltLfsrNativeAvx18
import BulksketchBridge.AvxScalarDelegates

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime
open Algebra.Gf64 Reconciliation DenseCoefficient
open bulksketch.backend.contract bulksketch.backend.portable
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear odd_recurrence_matches insert_nonzero)

set_option maxRecDepth 4096

/-- Exact rebuilt verifier at degree eighteen using the original public AVX
seed dispatch and original four-register tile. -/
def ActualRebuiltLfsrNativeAvx18AllCallbacks : Prop :=
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
      roots.length = 18 → 18 ≤ odd.length → 18 ≤ expected.length → 18 < coefficients.length →
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr avxField kernels roots odd coefficients expected =
          .ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_native_avx18_all_callbacks : ActualRebuiltLfsrNativeAvx18AllCallbacks := by
  intro load store loadLaw storeLaw portable one18 one32 single sparse K kernels linearEq recurrenceEq insertEq squareEq
  exact rebuilt_lfsr_native_avx18 load store loadLaw storeLaw portable one18 one32 single sparse kernels
    linearEq recurrenceEq insertEq (AvxScalarDelegates.rebuilt_square_law kernels squareEq)

#print axioms rebuilt_lfsr_native_avx18_all_callbacks

end BulksketchBridge.RebuiltLfsr
