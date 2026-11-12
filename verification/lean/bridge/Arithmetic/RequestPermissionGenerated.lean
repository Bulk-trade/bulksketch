-- Original checked request permission declarations.
import Arithmetic.FrozenShapeGenerated
import Arithmetic.ShapePermissionGenerated

open Aeneas Aeneas.Std Result Error

namespace bulksketch

/-- [bulksketch::sketch::api::DecodeLimits]
    Source: 'src/sketch/api.rs', lines 21:0-30:1
    Visibility: public -/
structure sketch.api.DecodeLimits where
  max_output_per_bucket : Std.Usize
  max_candidate_inputs : Std.Usize
  max_work : types.WorkUnits
  max_scratch_bytes : Std.Usize

/-- [bulksketch::sketch::wire::SketchView]
    Source: 'src/sketch/wire/mod.rs', lines 29:0-35:1
    Visibility: public -/
structure sketch.wire.SketchView (F : Type _) where
  bytes : Slice Std.U8
  buckets : Std.Usize
  words : Std.Usize
  payload_start : Std.Usize
  field : core.marker.PhantomData F

/-- [bulksketch::sketch::plan::DecodePlan]
    Source: 'src/sketch/plan.rs', lines 14:0-16:1
    Visibility: public -/
structure sketch.plan.DecodePlan where
  version : Std.U8

/-- [bulksketch::sketch::api::DecodeRequest]
    Source: 'src/sketch/api.rs', lines 34:0-45:1
    Visibility: public -/
structure sketch.api.DecodeRequest (F : Type _) where
  «local» : sketch.state.FrozenSketch F
  remote : sketch.wire.SketchView F
  candidates : Slice Std.U64
  plan : sketch.plan.DecodePlan
  limits : sketch.api.DecodeLimits

/-- [bulksketch::sketch::input::DecodeRowsRequest]
    Source: 'src/sketch/input.rs', lines 32:0-39:1
    Visibility: public -/
structure sketch.input.DecodeRowsRequest (F : Type _) where
  rows : Slice (sketch.input.DecodeRow F)
  plan : sketch.plan.DecodePlan
  limits : sketch.api.DecodeLimits

/-- [bulksketch::sketch::input::{impl bulksketch::sketch::input::RequestInput<F> for bulksketch::sketch::api::DecodeRequest<'_0, F>}::permits_id]:
    Source: 'src/sketch/input.rs', lines 132:4-134:5
    Visibility: public -/
def sketch.api.DecodeRequest.Insts.BulksketchSketchInputRequestInput.permits_id
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.api.DecodeRequest F) (bucket : Std.Usize) (id : Std.U64) :
  Result Bool
  := do
  let ss ← sketch.state.FrozenSketch.shape fieldBinaryFieldInst self.local
  sketch.shape.SketchShape.permits_id fieldBinaryFieldInst ss bucket id

/-- [bulksketch::sketch::input::{impl bulksketch::sketch::input::RequestInput<F> for bulksketch::sketch::input::DecodeRowsRequest<'_0, F>}::permits_id]:
    Source: 'src/sketch/input.rs', lines 196:4-198:5
    Visibility: public -/
def
  sketch.input.DecodeRowsRequest.Insts.BulksketchSketchInputRequestInput.permits_id
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.input.DecodeRowsRequest F) (bucket : Std.Usize) (id : Std.U64)
  :
  Result Bool
  := do
  let dr ← Slice.index_usize self.rows bucket
  let ss ← sketch.state.FrozenSketch.shape fieldBinaryFieldInst dr.local
  sketch.shape.SketchShape.permits_id fieldBinaryFieldInst ss 0#usize id

end bulksketch
