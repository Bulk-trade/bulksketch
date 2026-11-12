import BulksketchBridge.AvxEncodeCorrect
import BulksketchBridge.NativeVerificationBackendAcceptance

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 RebuiltLfsr DegreeProbeRuntime
open AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime AvxEncodeEntry
open bulksketch.backend.contract
open bulksketch.backend.portable (Portable)
open bulksketch.backend.x86_vpclmul512
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear odd_recurrence_matches)

/-- The paid verification binds both source branches, with exact native AVX
encode dispatch and explicit register-memory and specialized singleton laws. -/
def ActualNativeAvxPaidVerificationWithEncoder : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
      (one32 : Single), SingleLaw one32 32 →
    ∀ (single : SingleCapacity), SingleLaw (single 72#usize) 72 → SingleLaw (single 89#usize) 89 →
    ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    kernels.multiply_linear = multiply_linear load store portable avxField →
    kernels.odd_recurrence_matches = odd_recurrence_matches load portable avxField →
    kernels.insert_nonzero = nativeInsert load store one32 single avxField →
    kernels.encode_nonzero = nativeEncode load store one32 single →
    kernels.ArithmeticInst.square =
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.square avxField →
    (∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y) →
    ActualPaidVerificationAccepts kernels

theorem native_avx_paid_verification_with_encoder : ActualNativeAvxPaidVerificationWithEncoder := by
  intro load store loadLaw storeLaw portable one32 law32 single law72 law89 K kernels
    linear recurrence insert encode square mul
  refine native_avx_paid_verification load store loadLaw storeLaw portable
    (insert_18 (single_bases INSERT_BASES load) load store) one32 single
    (nativeSparse load store one32 single) kernels linear recurrence insert square mul ?_
  intro odd ids
  rw [encode]
  exact native_avx_encoding load store loadLaw storeLaw one32 law32 single law72 law89 odd ids

#print axioms native_avx_paid_verification_with_encoder

end BulksketchBridge.ExecutionDriver
