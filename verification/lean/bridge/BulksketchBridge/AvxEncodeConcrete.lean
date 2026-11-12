import BulksketchBridge.AvxEncodeVerification
import BulksketchBridge.AvxSingleton

namespace BulksketchBridge.AvxEncodeEntry

open Aeneas.Std AvxSquareRuntime AvxSquare AvxInsertDispatchRuntime
open bulksketch.backend.x86_vpclmul512

def concreteOne32 (load : Load) (store : Store) : Single :=
  insert_32 (single_bases INSERT_BASES load) load store

def concreteSingle (load : Load) (store : Store) : SingleCapacity :=
  insert_single (single_bases INSERT_BASES load) load store

def concreteEncode (load : Load) (store : Store) : Batch :=
  nativeEncode load store (concreteOne32 load store) (concreteSingle load store)

/-- Complete original GF64 encoder, with all reachable leaf bodies bound.
Load and store remain explicit checked register/memory interfaces. -/
def ActualConcreteNativeAvxEncoding : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ odd ids, concreteEncode load store odd ids = .ok (DegreeProbeRuntime.encodedWords odd ids)

theorem concrete_native_avx_encoding : ActualConcreteNativeAvxEncoding := by
  intro load store loadLaw storeLaw
  exact native_avx_encoding load store loadLaw storeLaw (concreteOne32 load store)
    (AvxSingleton.native_avx_singleton32 load store loadLaw storeLaw) (concreteSingle load store)
    (AvxSingleton.native_avx_singleton load store loadLaw storeLaw 72#usize (.inl rfl))
    (AvxSingleton.native_avx_singleton load store loadLaw storeLaw 89#usize (.inr rfl))

#print axioms concrete_native_avx_encoding

end BulksketchBridge.AvxEncodeEntry

namespace BulksketchBridge.ExecutionDriver

open Aeneas.Std Algebra.Gf64 RebuiltLfsr DegreeProbeRuntime
open AvxSquareRuntime AvxSquare AvxEncodeEntry
open bulksketch.backend.contract
open bulksketch.backend.portable (Portable)
open bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels
  (multiply_linear odd_recurrence_matches)

/-- Both paid AVX verification branches with the exact native encoder
bound in the full branch and the native tile seed in the rebuilt branch. -/
def ActualNativeAvxPaidVerificationConcreteEncoder : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (portable : {F : Type} → bulksketch.field.BinaryField F → BulkKernels Portable F)
      {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64),
    kernels.multiply_linear = multiply_linear load store portable avxField →
    kernels.odd_recurrence_matches = odd_recurrence_matches load portable avxField →
    kernels.insert_nonzero = nativeInsert load store (concreteOne32 load store) (concreteSingle load store) avxField →
    kernels.encode_nonzero = concreteEncode load store →
    kernels.ArithmeticInst.square =
      bulksketch.backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractArithmetic.square avxField →
    (∀ x y, kernels.ArithmeticInst.mul x y = bulksketch.field.gf64.mul fieldDictionary x y) →
    ActualPaidVerificationAccepts kernels

theorem native_avx_paid_verification_concrete_encoder : ActualNativeAvxPaidVerificationConcreteEncoder := by
  intro load store loadLaw storeLaw portable
  exact native_avx_paid_verification_with_encoder load store loadLaw storeLaw portable
    (concreteOne32 load store) (AvxSingleton.native_avx_singleton32 load store loadLaw storeLaw)
    (concreteSingle load store)
    (AvxSingleton.native_avx_singleton load store loadLaw storeLaw 72#usize (.inl rfl))
    (AvxSingleton.native_avx_singleton load store loadLaw storeLaw 89#usize (.inr rfl))

#print axioms native_avx_paid_verification_concrete_encoder

end BulksketchBridge.ExecutionDriver
