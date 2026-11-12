import BulksketchBridge.NativeFullVerificationAcceptance
import BulksketchBridge.NativeRebuiltVerificationAcceptance
import BulksketchBridge.ConcreteRebuiltDictionaries
import BulksketchBridge.RebuiltLfsrNativeAvxAllDegrees

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 ExecutionDriverRuntime DegreeProbeRuntime RebuiltLfsr Reconciliation
open bulksketch.backend.contract bulksketch.decode.stages bulksketch.decode.row
open bulksketch.decode.scratch bulksketch.types

structure PaidVerificationReady {K : Type} (before : RootDrainState K) (input : RowInput)
    (paid : WorkMeter) : Prop where
  running : before.execution.state = .Running .Verification
  noProbe : before.execution.degree_probe = none
  charged : StageCharge.chargeResult before.meter (ExecutionVerify.actualCost before.execution input) =
    (.Ok (), paid)
  rootRoom : before.execution.roots.count.val ≤ before.workspace.roots.length
  distinct : (ExecutionVerify.selectedRoots before.execution before.workspace).val.Nodup
  rebuilt : ExecutionVerify.selects before.execution input = true →
    let roots := ExecutionVerify.selectedRoots before.execution before.workspace
    (0 : Field) ∉ rootSupport roots ∧ roots.length < before.workspace.bm.length ∧
      min roots.length input.difference.length ≤ before.workspace.verification.length
  full : ExecutionVerify.selects before.execution input = false →
    ProbeVerification.Bounds input.difference (ExecutionVerify.selectedRoots before.execution before.workspace)
      before.workspace.verification

/-- The exact paid driver accepts the same syndromes in either verifier
branch. The source branch's different scratch frames remain in the result. -/
def ActualPaidVerificationAccepts {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64) : Prop :=
  ∀ (before : RootDrainState K) (input : RowInput) (paid : WorkMeter),
    PaidVerificationReady before input paid →
    ∃ seed continued,
      let lower := ExecutionVerify.expected before.execution input before.workspace before.meter
        (ExecutionVerify.actualCost before.execution input) seed continued
      let after := transition .Verification lower
      nativeCandidateDriver nativeCanonicalize kernels before.execution input before.workspace before.meter = .ok after ∧
      (after.2.1.state = .Running .Canonicalization ↔ ∀ i < input.difference.length,
        toField input.difference[i]!.bv =
          oddSyndrome (rootSupport (ExecutionVerify.selectedRoots before.execution before.workspace)) i)

theorem native_paid_verification_accepts {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y)
    (linear : linearLaw kernels) (square : squaringLaw kernels) (recurrence : ContinuationLaw kernels)
    (seedLaw : RebuiltSeedLaw kernels) (encoding : CorrectEncoding kernels) :
    ActualPaidVerificationAccepts kernels := by
  intro before input paid ready
  cases selected : ExecutionVerify.selects before.execution input
  · exact ⟨before.workspace.verification, false,
      native_full_verification_accepts nativeCanonicalize kernels mul square encoding before input paid
        ready.running ready.noProbe selected ready.charged ready.rootRoom ready.distinct (ready.full selected)⟩
  · obtain ⟨nonzero, coefficientRoom, seedRoom⟩ := ready.rebuilt selected
    exact native_rebuilt_verification_accepts nativeCanonicalize kernels linear square recurrence seedLaw
      before input paid ready.running ready.noProbe selected ready.charged ready.rootRoom
      ready.distinct nonzero coefficientRoom seedRoom

private theorem native_scalar_paid_verification {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : ∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y)
    (square : squaringLaw kernels) (arithmetic : OddRecurrence.CorrectArithmetic kernels)
    (linear : kernels.multiply_linear = BulkKernels.multiply_linear.default kernels)
    (recurrence : kernels.odd_recurrence_matches = BulkKernels.odd_recurrence_matches.default kernels)
    (encode : kernels.encode_nonzero = BulkKernels.encode_nonzero.default kernels)
    (insert : ∀ shape roots, kernels.insert_nonzero shape roots =
      bulksketch.backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
        fieldDictionary shape roots) : ActualPaidVerificationAccepts kernels := by
  refine native_paid_verification_accepts kernels mul ?_ square ?_ ?_ ?_
  · intro words root
    rw [linear]
    exact linear_default_matches kernels mul words root
  · intro odd locator nonempty
    rw [recurrence]
    exact OddRecurrence.default_refines kernels odd locator arithmetic nonempty
  · intro shape roots _ distinct
    rw [insert]
    exact PortableEncoding.rebuilt_seed shape roots distinct
  · exact encoding_of_portable_default kernels encode insert

def ActualNativePortablePaidVerification : Prop := ActualPaidVerificationAccepts portableKernels

theorem native_portable_paid_verification : ActualNativePortablePaidVerification := by
  exact native_scalar_paid_verification portableKernels (fun _ _ => rfl) (fun _ => rfl)
    ⟨fun _ _ => rfl, fun _ => rfl⟩ rfl rfl rfl (fun _ _ => rfl)

def ActualNativePclmulPaidVerification : Prop := ActualPaidVerificationAccepts pclmulKernels

theorem native_pclmul_paid_verification : ActualNativePclmulPaidVerification := by
  apply native_scalar_paid_verification pclmulKernels _ _ _ rfl rfl rfl X86Pclmul.native_pclmul_insert
  · intro x y
    exact (X86Pclmul.mul_refines x y).trans (native_mul_word x y).symm
  · intro input
    exact (X86Pclmul.square_refines input).trans (Square.square_refines input).symm
  · exact ⟨fun x y => (X86Pclmul.raw_mul_refines x y).trans (RawMul.raw_mul_refines x y).symm,
      fun _ => rfl⟩

open AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime
open bulksketch.backend.portable (Portable)
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear odd_recurrence_matches insert_nonzero)

def ActualNativeAvxPaidVerification : Prop :=
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
    (∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y) →
    CorrectEncoding kernels → ActualPaidVerificationAccepts kernels

theorem native_avx_paid_verification : ActualNativeAvxPaidVerification := by
  intro load store loadLaw storeLaw portable one18 one32 single sparse K kernels
    linear recurrence insert square mul encoding
  refine native_paid_verification_accepts kernels mul ?_
    (AvxScalarDelegates.rebuilt_square_law kernels square) ?_ ?_ encoding
  · intro words root
    rw [linear]
    exact AvxMultiplyLinear.native_avx_linear_entry load store loadLaw storeLaw portable avxField
      64#u32 words root (by simp [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField,
        bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS])
  · intro odd locator nonempty
    rw [recurrence]
    exact AvxRecurrence.native_avx_recurrence_entry_gf64 load loadLaw portable odd locator nonempty
  · intro shape roots fits distinct
    rw [insert]
    exact AvxRebuiltSeed.native_avx_rebuilt_seed load loadLaw one18 one32 single sparse shape roots fits distinct

#print axioms native_portable_paid_verification
#print axioms native_pclmul_paid_verification
#print axioms native_avx_paid_verification

end BulksketchBridge.ExecutionDriver
