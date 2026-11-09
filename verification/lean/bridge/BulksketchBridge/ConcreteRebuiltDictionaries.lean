import Arithmetic.DefaultWireDifferenceDictionariesGenerated
import BulksketchBridge.RebuiltLfsrNativePortableAllDegrees
import BulksketchBridge.RebuiltLfsrNativePclmulAllDegrees

namespace BulksketchBridge.RebuiltLfsr

open Aeneas.Std Algebra.Gf64 Reconciliation
open bulksketch.backend.portable (Portable)
open bulksketch.backend.x86_pclmul (Pclmul)

abbrev portableKernels := Portable.Insts.BulksketchBackendContractBulkKernels portableField
abbrev pclmulKernels := Pclmul.Insts.BulksketchBackendContractBulkKernels pclmulField

def ActualRebuiltLfsrConcretePortableAllDegrees : Prop :=
  ∀ (roots odd coefficients expected : Slice U64),
    roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
    roots.length < coefficients.length →
    min roots.length odd.length ≤ expected.length →
    ∃ accepted updatedCoefficients updatedExpected,
      bulksketch.decode.verify.rebuilt_lfsr portableField portableKernels roots odd coefficients expected =
        .ok (accepted, updatedCoefficients, updatedExpected) ∧
      (accepted = true ↔ ∀ i, i < odd.length →
        toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_concrete_portable_all_degrees : ActualRebuiltLfsrConcretePortableAllDegrees := by
  exact rebuilt_lfsr_native_portable_all_degrees portableKernels rfl rfl rfl rfl rfl rfl rfl

def ActualRebuiltLfsrConcretePclmulAllDegrees : Prop :=
  ∀ (roots odd coefficients expected : Slice U64),
    roots.val.Nodup → (0 : Field) ∉ rootSupport roots →
    roots.length < coefficients.length →
    min roots.length odd.length ≤ expected.length →
    ∃ accepted updatedCoefficients updatedExpected,
      bulksketch.decode.verify.rebuilt_lfsr pclmulField pclmulKernels roots odd coefficients expected =
        .ok (accepted, updatedCoefficients, updatedExpected) ∧
      (accepted = true ↔ ∀ i, i < odd.length →
        toField odd[i]!.bv = oddSyndrome (rootSupport roots) i)

theorem rebuilt_lfsr_concrete_pclmul_all_degrees : ActualRebuiltLfsrConcretePclmulAllDegrees := by
  exact rebuilt_lfsr_native_pclmul_all_degrees pclmulKernels rfl rfl rfl rfl rfl rfl rfl

#print axioms rebuilt_lfsr_concrete_portable_all_degrees
#print axioms rebuilt_lfsr_concrete_pclmul_all_degrees

end BulksketchBridge.RebuiltLfsr
