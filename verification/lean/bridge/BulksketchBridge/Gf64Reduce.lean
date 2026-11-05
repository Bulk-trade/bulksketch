import BulksketchBridge.Gf64ReduceSpec
import BulksketchBridge.Reduce

namespace BulksketchBridge.Gf64Reduce

open Aeneas.Std

/-- The actual source-generated Gf64 dictionary closes the branch condition.
Every two-word input returns the exact remainder and its polynomial certificate;
no dictionary or successful-return assumption remains in this endpoint.
-/
theorem reduce_refines : ReturnsFoldAndCertificate := by
  intro product
  obtain ⟨output, normal, exactBits⟩ :=
    BulksketchBridge.Reduce.reduce64_refines
      bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField product (by
        simp only [bulksketch.field.Gf64.Insts.BulksketchFieldBinaryField.BITS])
  refine ⟨output, normal, exactBits, ?_⟩
  rw [exactBits]
  exact BulksketchProofs.Field.reduction_division_certificate product.lo.bv product.hi.bv

end BulksketchBridge.Gf64Reduce
