import BulksketchBridge.RebuiltLfsrPortable
import BulksketchBridge.Portable

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std Algebra.Gf64 Reconciliation
open bulksketch.backend.contract
open bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractArithmetic (mul raw_mul reduce square)

abbrev portableField := bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField

/-- Bind every rebuilt verifier callback to its original Portable source
body. The acceptance theorem applies at every admitted GF64 degree. -/
def ActualRebuiltLfsrNativePortableAllDegrees : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    kernels.ArithmeticInst.mul = mul portableField →
    kernels.ArithmeticInst.square = square portableField →
    kernels.ArithmeticInst.raw_mul = raw_mul portableField →
    kernels.ArithmeticInst.reduce = reduce portableField →
    kernels.multiply_linear = BulkKernels.multiply_linear.default kernels →
    kernels.odd_recurrence_matches = BulkKernels.odd_recurrence_matches.default kernels →
    kernels.insert_nonzero =
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero portableField →
    ∀ (roots odd coefficients expected : Slice U64),
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr portableField kernels roots odd coefficients expected =
          .ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_native_portable_all_degrees : ActualRebuiltLfsrNativePortableAllDegrees := by
  intro K kernels mulEq squareEq rawEq reduceEq linearEq recurrenceEq insertEq
  have nativeMul : ∀ a b, kernels.ArithmeticInst.mul a b =
      bulksketch.field.gf64.mul portableField a b := by
    intro a b
    rw [mulEq]
    rfl
  have squareLaw : squaringLaw kernels := by
    intro input
    rw [squareEq]
    rfl
  have arithmetic : OddRecurrence.CorrectArithmetic kernels := by
    constructor
    · intro a b
      rw [rawEq]
      rfl
    · intro input
      rw [reduceEq]
      rfl
  exact rebuilt_lfsr_portable_seed_refines kernels nativeMul linearEq squareLaw arithmetic recurrenceEq insertEq

#print axioms rebuilt_lfsr_native_portable_all_degrees

end BulksketchBridge.RebuiltLfsr
