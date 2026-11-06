import BulksketchBridge.InverseChallenges
import BulksketchBridge.InverseMath

namespace BulksketchBridge.Inverse

open Aeneas Aeneas.Std BulksketchBridge.Algebra.Gf64

/-- Frozen full-source operational endpoint, with the generic API's explicit
universal callback normal-result contracts. -/
theorem exact_chain_refines : InverseChallenges.actualSourceReturnsExactChain := by
  intro T1 T2 mulDict frobDict mulCallback frobCallback multiply frobenius mulNormal frobNormal input
  exact normal_refines mulDict frobDict mulCallback frobCallback multiply frobenius
    mulNormal frobNormal input

/-- The actual generated inversion body computes exactly the represented
Mathlib field inverse on nonzero inputs and None on zero. Native arithmetic
refinements discharge all callback behavior; inverse_using's separately
unsupported borrowed closure is not part of this endpoint. -/
theorem field_inverse_refines : InverseChallenges.actualSourceReturnsFieldInverse := by
  intro T1 T2 mulDict frobDict mulCallback frobCallback mulNative frobNative input
  have mulNormal : MulNormal mulDict mulCallback multiplyNativeWord := by
    intro left right
    rw [mulNative, native_mul_word]
    rfl
  have frobNormal : FrobeniusNormal frobDict frobCallback frobeniusNativeWord := by
    intro input count
    rw [frobNative, FrobeniusPeriod.native_unmodded_refines]
    rfl
  rw [normal_refines mulDict frobDict mulCallback frobCallback multiplyNativeWord
    frobeniusNativeWord mulNormal frobNormal input, expected_result_is_field_inverse]

/-- No hypothetical callback behavior is needed for this specialization: both
callbacks invoke the already-proved actual native generated bodies directly. -/
theorem native_callback_instance : InverseChallenges.nativeCallbackInstanceReturnsFieldInverse := by
  intro input
  apply field_inverse_refines
  · intro left right
    rfl
  · intro value count
    rfl

end BulksketchBridge.Inverse
