-- Checked original SketchShape permission declaration.
import Arithmetic.CandidateCompactGenerated

open Aeneas Aeneas.Std Result Error

namespace bulksketch

/-- [bulksketch::sketch::shape::{bulksketch::sketch::shape::SketchShape<F>}::permits_id]:
    Source: 'src/sketch/shape.rs', lines 115:4-117:5
    Visibility: public -/
def sketch.shape.SketchShape.permits_id
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.shape.SketchShape F) (bucket : Std.Usize) (id : Std.U64) :
  Result Bool
  := do
  let i ← sketch.shape.SketchShape.bucket_count fieldBinaryFieldInst self
  if bucket < i
  then
    let i1 ← sketch.shape.SketchShape.bucket_for fieldBinaryFieldInst self id
    ok (i1 = bucket)
  else ok false

end bulksketch
