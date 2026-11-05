import BulksketchBridge.ReduceSpec
import BulksketchProofs.Field.Reduction

namespace BulksketchBridge.Reduce

open Aeneas.Std

/-- Every raw input returns normally from the unchanged GF64 branch, with the
complete remainder word. Constants for other dictionary fields are unrestricted. -/
theorem reduce64_refines : RefinesGF64 := by
  intro F dictionary product bits
  refine ⟨⟨BulksketchProofs.Field.reduceFold64 product.lo.bv product.hi.bv⟩, ?_, rfl⟩
  have shr63 (word : U64) : word >>> 63#i32 = Result.ok (⟨word.bv >>> 63⟩ : U64) := by rfl
  have shr61 (word : U64) : word >>> 61#i32 = Result.ok (⟨word.bv >>> 61⟩ : U64) := by rfl
  have shr60 (word : U64) : word >>> 60#i32 = Result.ok (⟨word.bv >>> 60⟩ : U64) := by rfl
  have shl1 (word : U64) : word <<< 1#i32 = Result.ok (⟨word.bv <<< 1⟩ : U64) := by rfl
  have shl3 (word : U64) : word <<< 3#i32 = Result.ok (⟨word.bv <<< 3⟩ : U64) := by rfl
  have shl4 (word : U64) : word <<< 4#i32 = Result.ok (⟨word.bv <<< 4⟩ : U64) := by rfl
  simp only [bulksketch.field.gf64.reduce, bits, bind_ok, ite_true, lift,
    shr63, shr61, shr60, shl1, shl3, shl4]
  change Result.ok (⟨BulksketchProofs.Generated.reduceGf64 product.lo.bv product.hi.bv⟩ : U64) =
    Result.ok (⟨BulksketchProofs.Field.reduceFold64 product.lo.bv product.hi.bv⟩ : U64)
  rw [BulksketchProofs.Field.generated_reduce_eq_model]

/-- The actual generated GF64 branch supplies the existing universal polynomial
division certificate, without changing its source branch or assuming success. -/
theorem reduce64_division_certificate : DivisionCertificateGF64 := by
  intro F dictionary product bits
  obtain ⟨output, normal, exactBits⟩ := reduce64_refines dictionary product bits
  refine ⟨output, normal, ?_⟩
  rw [exactBits]
  exact BulksketchProofs.Field.reduction_division_certificate product.lo.bv product.hi.bv

end BulksketchBridge.Reduce
