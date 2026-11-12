import Arithmetic.RequestPermissionGenerated
import BulksketchBridge.ShapePermission
import BulksketchBridge.FrozenShape

namespace BulksketchBridge.RequestPermission

open Aeneas Aeneas.Std Result Error
open bulksketch.sketch.api bulksketch.sketch.input bulksketch.sketch.state

abbrev Field := bulksketch.field.BinaryField

def ActualDecodeRequestPermits : Prop :=
  ∀ {F : Type} (field : Field F) (self : DecodeRequest F) (bucket : Usize) (id : U64),
    DecodeRequest.Insts.BulksketchSketchInputRequestInput.permits_id field self bucket id =
      .ok (ShapePermission.allowed self.local.state.shape bucket id)

theorem decode_request_permits_refines : ActualDecodeRequestPermits := by
  intro F field self bucket id
  rw [DecodeRequest.Insts.BulksketchSketchInputRequestInput.permits_id,
    FrozenShape.frozen_shape_refines field self.local, bind_ok, ShapePermission.shape_permits_id_refines]

def expectedRows {F : Type} (self : DecodeRowsRequest F) (bucket : Usize) (id : U64) : Result Bool :=
  match self.rows.val[bucket.val]? with
  | none => .fail .arrayOutOfBounds
  | some row => .ok (ShapePermission.allowed row.local.state.shape 0#usize id)

def ActualDecodeRowsRequestPermits : Prop :=
  ∀ {F : Type} (field : Field F) (self : DecodeRowsRequest F) (bucket : Usize) (id : U64),
    DecodeRowsRequest.Insts.BulksketchSketchInputRequestInput.permits_id field self bucket id =
      expectedRows self bucket id

theorem decode_rows_request_permits_refines : ActualDecodeRowsRequestPermits := by
  intro F field self bucket id
  have index : Slice.index_usize self.rows bucket =
      (match self.rows.val[bucket.val]? with
       | none => .fail .arrayOutOfBounds
       | some row => .ok row) := by
    simp only [Slice.index_usize, Slice.getElem?_Usize_eq]
    cases self.rows.val[bucket.val]? <;> rfl
  rw [DecodeRowsRequest.Insts.BulksketchSketchInputRequestInput.permits_id, index]
  unfold expectedRows
  cases self.rows.val[bucket.val]? with
  | none => simp only [bind_fail]
  | some row =>
    rw [bind_ok, FrozenShape.frozen_shape_refines field row.local, bind_ok, ShapePermission.shape_permits_id_refines]

#print axioms decode_request_permits_refines
#print axioms decode_rows_request_permits_refines

end BulksketchBridge.RequestPermission
