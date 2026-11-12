import Arithmetic.ShapePermissionGenerated
import BulksketchBridge.CandidateBucket

namespace BulksketchBridge.ShapePermission

open Aeneas Aeneas.Std Result
open bulksketch.sketch.shape

def ActualShapeBucketCount : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F),
    SketchShape.bucket_count field shape = .ok shape.capacities.len

theorem shape_bucket_count_refines : ActualShapeBucketCount := fun _ _ => rfl

def allowed {F : Type} (shape : SketchShape F) (bucket : Usize) (id : U64) : Bool :=
  decide (bucket.val < shape.capacities.length ∧ id.val % shape.capacities.length = bucket.val)

/-- The original shape guard rejects invalid buckets before modulo and
permits precisely the IDs that route to the given valid bucket. -/
def ActualShapePermitsId : Prop :=
  ∀ {F : Type} (field : bulksketch.field.BinaryField F) (shape : SketchShape F)
    (bucket : Usize) (id : U64),
    SketchShape.permits_id field shape bucket id = .ok (allowed shape bucket id)

theorem shape_permits_id_refines : ActualShapePermitsId := by
  intro F field shape bucket id
  rw [SketchShape.permits_id, shape_bucket_count_refines field shape, bind_ok]
  have width : bucket < shape.capacities.len ↔ bucket.val < shape.capacities.length := by
    change bucket.val < shape.capacities.len.val ↔ _
    rw [Slice.len_val]
  by_cases inside : bucket.val < shape.capacities.length
  · obtain ⟨routed, ran, exactVal, _⟩ :=
      CandidateNormalization.native_candidate_bucket field shape id (by omega)
    have same : routed = bucket ↔ id.val % shape.capacities.length = bucket.val := by
      rw [← exactVal]
      exact ⟨congrArg UScalar.val, UScalar.eq_of_val_eq⟩
    simp only [ite_eq_left (width.mpr inside), ran, bind_ok, allowed, inside, true_and, same]
  · simp only [ite_eq_right (fun valid => inside (width.mp valid)), allowed, inside, false_and,
      decide_false]

#print axioms shape_bucket_count_refines
#print axioms shape_permits_id_refines

end BulksketchBridge.ShapePermission
