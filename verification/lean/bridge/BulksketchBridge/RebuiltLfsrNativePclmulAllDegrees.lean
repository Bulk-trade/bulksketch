import BulksketchBridge.X86PclmulInsert
import BulksketchBridge.RebuiltLfsrPortable
import BulksketchBridge.AvxScalarDelegates

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std Algebra.Gf64 Reconciliation
open bulksketch.backend.contract
open bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic
  (mul square raw_mul reduce)
open bulksketch.backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels (insert_nonzero)

abbrev pclmulField := X86Pclmul.dictionary

/-- Bind the exact PCLMUL insertion, arithmetic and inherited original
scalar defaults to the rebuilt verifier at every admitted degree. -/
def ActualRebuiltLfsrNativePclmulAllDegrees : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    kernels.ArithmeticInst.mul = mul pclmulField →
    kernels.ArithmeticInst.square = square pclmulField →
    kernels.ArithmeticInst.raw_mul = raw_mul pclmulField →
    kernels.ArithmeticInst.reduce = reduce pclmulField →
    kernels.multiply_linear = BulkKernels.multiply_linear.default kernels →
    kernels.odd_recurrence_matches = BulkKernels.odd_recurrence_matches.default kernels →
    kernels.insert_nonzero = insert_nonzero pclmulField →
    ∀ (roots odd coefficients expected : Slice U64),
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr pclmulField kernels roots odd coefficients expected =
          .ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_native_pclmul_all_degrees : ActualRebuiltLfsrNativePclmulAllDegrees := by
  intro K kernels mulEq squareEq rawEq reduceEq linearEq recurrenceEq insertEq
  have nativeMul : ∀ a b, kernels.ArithmeticInst.mul a b =
      bulksketch.field.gf64.mul pclmulField a b := by
    intro a b
    rw [mulEq]
    exact (X86Pclmul.mul_refines a b).trans (native_mul_word a b).symm
  have squareLaw : squaringLaw kernels := by
    intro input
    rw [squareEq]
    exact (X86Pclmul.square_refines input).trans (Square.square_refines input).symm
  have arithmetic : OddRecurrence.CorrectArithmetic kernels := by
    constructor
    · intro a b
      rw [rawEq]
      exact (X86Pclmul.raw_mul_refines a b).trans (RawMul.raw_mul_refines a b).symm
    · intro input
      rw [reduceEq]
      rfl
  have portableSeed : kernels.insert_nonzero =
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero pclmulField := by
    rw [insertEq]
    funext odd ids
    exact X86Pclmul.native_pclmul_insert odd ids
  exact rebuilt_lfsr_portable_seed_refines kernels nativeMul linearEq squareLaw arithmetic recurrenceEq portableSeed

#print axioms rebuilt_lfsr_native_pclmul_all_degrees

end BulksketchBridge.RebuiltLfsr
