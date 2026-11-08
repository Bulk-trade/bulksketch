import BulksketchBridge.RebuiltLfsrAcceptance
import BulksketchBridge.PortableRebuiltSeed

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std Algebra.Gf64 DenseCoefficient Reconciliation
open bulksketch.backend.contract

/-- Actual rebuilt verifier acceptance when the backend dictionary selects
the proved original Portable seed, default locator update and scalar
continuation. Each arithmetic callback retains its explicit GF64 contract. -/
def ActualRebuiltLfsrWithPortableSeed : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    (∀ a b, kernels.ArithmeticInst.mul a b =
      bulksketch.field.gf64.mul bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField a b) →
    kernels.multiply_linear = BulkKernels.multiply_linear.default kernels →
    squaringLaw kernels → OddRecurrence.CorrectArithmetic kernels →
    kernels.odd_recurrence_matches = BulkKernels.odd_recurrence_matches.default kernels →
    kernels.insert_nonzero =
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField →
    ∀ (roots odd coefficients expected : Slice U64),
      roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
      roots.length < coefficients.length →
      min roots.length odd.length ≤ expected.length →
      ∃ accepted updatedCoefficients updatedExpected,
        bulksketch.decode.verify.rebuilt_lfsr
          bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField kernels roots odd coefficients expected =
          Result.ok (accepted, updatedCoefficients, updatedExpected) ∧
        (accepted = true ↔ ∀ i, i < odd.length →
          toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_portable_seed_refines : ActualRebuiltLfsrWithPortableSeed := by
  intro K kernels nativeMul update square arithmetic recurrence insert roots odd coefficients expected
    distinct noZero room expectedRoom
  have linear : linearLaw kernels := by
    intro words root
    rw [update]
    exact linear_default_matches kernels nativeMul words root
  let shape := prefixSlice expected (min roots.length odd.length)
  obtain ⟨seed, normal, length, fieldWords⟩ := PortableEncoding.rebuilt_seed shape roots distinct
  have seedLength : seed.length = min roots.length odd.length := by
    simpa [shape, Nat.min_eq_left expectedRoom] using length
  have seedCallback : kernels.insert_nonzero (zeroWords (prefixSlice expected seed.length)) roots =
      Result.ok seed := by
    rw [insert, seedLength]
    exact normal
  exact rebuilt_lfsr_iff_direct kernels linear square arithmetic recurrence roots odd coefficients expected
    seed distinct noZero room expectedRoom seedLength seedCallback fieldWords

end BulksketchBridge.RebuiltLfsr
