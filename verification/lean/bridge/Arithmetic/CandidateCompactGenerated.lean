-- Original checked shape and candidate compaction projections.
import Arithmetic.Funs
import Arithmetic.ReconstructionTypes

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

/-- [bulksketch::sketch::shape::SketchShape]
    Source: 'src/sketch/shape.rs', lines 27:0-32:1
    Visibility: public -/
structure sketch.shape.SketchShape (F : Type _) where
  capacities : Slice Std.U16
  total_words : Std.Usize
  wire_bytes : Std.Usize
  field : core.marker.PhantomData F

/-- [bulksketch::sketch::shape::{bulksketch::sketch::shape::SketchShape<F>}::bucket_count]:
    Source: 'src/sketch/shape.rs', lines 88:4-90:5
    Visibility: public -/
def sketch.shape.SketchShape.bucket_count
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.shape.SketchShape F) :
  Result Std.Usize
  := do
  ok (Slice.len self.capacities)

/-- [bulksketch::sketch::shape::{bulksketch::sketch::shape::SketchShape<F>}::bucket_for]:
    Source: 'src/sketch/shape.rs', lines 109:4-111:5
    Visibility: public -/
def sketch.shape.SketchShape.bucket_for
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (self : sketch.shape.SketchShape F) (id : Std.U64) :
  Result Std.Usize
  := do
  let i ← sketch.shape.SketchShape.bucket_count fieldBinaryFieldInst self
  let i1 ← lift (UScalar.cast .U64 i)
  let i2 ← id % i1
  let r ← Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from i2
  core.result.Result.expect core.num.error.TryFromIntError.Insts.CoreFmtDebug r
    (toStr "remainder fits row count")

/-- [bulksketch::sketch::candidates::normalize]: loop body 3:
    Source: 'src/sketch/candidates.rs', lines 52:4-59:5 -/
@[rust_loop_body]
def sketch.candidates.normalize_loop1.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (shape : sketch.shape.SketchShape F) (iter : core.ops.range.Range Std.Usize)
  (offsets : Slice Std.U64) (ids : Slice Std.U64) (used : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U64) ×
    (Slice Std.U64) × Std.Usize) ((Slice Std.U64) × (Slice Std.U64)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (offsets, ids))
  | some index =>
    let id ← Slice.index_usize ids index
    if id != 0#u64
    then
      if used = 0#usize
      then
        let s ← Slice.update ids used id
        let used1 ← used + 1#usize
        let i ←
          sketch.shape.SketchShape.bucket_for fieldBinaryFieldInst shape id
        let i1 ← i + 1#usize
        let i2 ← Slice.index_usize offsets i1
        let i3 ← i2 + 1#u64
        let s1 ← Slice.update offsets i1 i3
        ok (cont (iter1, s1, s, used1))
      else
        let i ← used - 1#usize
        let i1 ← Slice.index_usize ids i
        if i1 != id
        then
          let s ← Slice.update ids used id
          let used1 ← used + 1#usize
          let i2 ←
            sketch.shape.SketchShape.bucket_for fieldBinaryFieldInst shape id
          let i3 ← i2 + 1#usize
          let i4 ← Slice.index_usize offsets i3
          let i5 ← i4 + 1#u64
          let s1 ← Slice.update offsets i3 i5
          ok (cont (iter1, s1, s, used1))
        else ok (cont (iter1, offsets, ids, used))
    else ok (cont (iter1, offsets, ids, used))

/-- [bulksketch::sketch::candidates::normalize]: loop 3:
    Source: 'src/sketch/candidates.rs', lines 52:4-59:5 -/
@[rust_loop]
def sketch.candidates.normalize_loop1
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.ops.range.Range Std.Usize) (shape : sketch.shape.SketchShape F)
  (offsets : Slice Std.U64) (ids : Slice Std.U64) (used : Std.Usize) :
  Result ((Slice Std.U64) × (Slice Std.U64))
  := do
  loop
    (fun (iter1, offsets1, ids1, used1) =>
      sketch.candidates.normalize_loop1.body fieldBinaryFieldInst shape iter1
      offsets1 ids1 used1)
    (iter, offsets, ids, used)

/-- [bulksketch::sketch::candidates::normalize]: loop body 4:
    Source: 'src/sketch/candidates.rs', lines 60:4-62:5 -/
@[rust_loop_body]
def sketch.candidates.normalize_loop2.body
  (iter : core.ops.range.Range Std.Usize) (offsets : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done offsets)
  | some bucket =>
    let i ← Slice.index_usize offsets bucket
    let i1 ← bucket + 1#usize
    let i2 ← Slice.index_usize offsets i1
    let i3 ← i2 + i
    let s ← Slice.update offsets i1 i3
    ok (cont (iter1, s))

/-- [bulksketch::sketch::candidates::normalize]: loop 4:
    Source: 'src/sketch/candidates.rs', lines 60:4-62:5 -/
@[rust_loop]
def sketch.candidates.normalize_loop2
  (iter : core.ops.range.Range Std.Usize) (offsets : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, offsets1) => sketch.candidates.normalize_loop2.body iter1
      offsets1)
    (iter, offsets)

end bulksketch
