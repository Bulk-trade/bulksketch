import Arithmetic.CandidateCompactGenerated
import BulksketchBridge.ClosedLeafAdvance

namespace BulksketchBridge.CandidateNormalization

open Aeneas Aeneas.Std Result
open bulksketch.sketch.shape

theorem usize_fits_u64 (value : Usize) : value.val < 2 ^ 64 :=
  value.hBounds.trans_le (Nat.pow_le_pow_right (by decide) System.Platform.numBits_le)

/-- Original modulo routing, including the exact usize/u64 conversions. -/
def ActualNativeCandidateBucket : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F) (id : U64),
    0 < shape.capacities.length →
    ∃ bucket : Usize,
      SketchShape.bucket_for field shape id = .ok bucket ∧
      bucket.val = id.val % shape.capacities.length ∧ bucket.val < shape.capacities.length

theorem native_candidate_bucket : ActualNativeCandidateBucket := by
  intro F field shape id positive
  let count := shape.capacities.len
  let wide := UScalar.cast .U64 count
  have wideVal : wide.val = shape.capacities.length := by
    unfold wide
    rw [UScalar.cast_val_eq]
    change count.val % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (usize_fits_u64 count)]
    exact Slice.len_val _
  obtain ⟨rem, remainder, remVal⟩ := RawMulTable.normal_of_spec _ _
    (U64.rem_spec id (y := wide) (by rw [wideVal]; omega))
  change rem.val = id.val % wide.val at remVal
  rw [wideVal] at remVal
  have cap : rem.val < shape.capacities.length := by rw [remVal]; exact Nat.mod_lt _ positive
  have fits : shape.capacities.length ≤ Usize.max := shape.capacities.length_ineq
  obtain ⟨bucket, converted, bucketVal⟩ := checked_unsigned_conversion_normal (target := .Usize) rem
    (by rw [UScalar.max_USize_eq]; omega)
  refine ⟨bucket, ?_, bucketVal.trans remVal, by omega⟩
  unfold SketchShape.bucket_for SketchShape.bucket_count
  simp only [bind_ok, lift]
  rw [show (id % UScalar.cast .U64 shape.capacities.len : Result U64) = .ok rem from remainder, bind_ok]
  rw [show Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from rem = .ok (.Ok bucket) from converted,
    bind_ok]
  rfl

#print axioms native_candidate_bucket

end BulksketchBridge.CandidateNormalization
