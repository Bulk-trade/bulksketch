-- Exact source merge and wrapper declarations, with scoped standard bindings.
import Arithmetic.CandidateCompactGenerated
import Arithmetic.PortableEncodingRuntime
import Arithmetic.DenseGcdGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace Aeneas.Std.CandidateMergeRuntime

/-- The pinned Rust tuple `PartialOrd::le` compares the first unsigned
coordinate and consults the second only on equality. This adapter is
used at the original, fixed unsigned dictionary call site. -/
def pairLE (_ : core.cmp.PartialOrd Usize Usize) (_ : core.cmp.PartialOrd U64 U64)
    (left right : Usize × U64) : Result Bool :=
  .ok (decide (left.1.val < right.1.val ∨ (left.1.val = right.1.val ∧ left.2.val ≤ right.2.val)))

end Aeneas.Std.CandidateMergeRuntime

namespace bulksketch

local notation "Pair.Insts.CoreCmpPartialOrdPair.le" => CandidateMergeRuntime.pairLE
local notation "core.mem.swap" => DenseGcdRuntime.swapSlots

/-- [bulksketch::sketch::candidates::normalize::{closure}]
    Source: 'src/sketch/candidates.rs', lines 19:14-19:45 -/
@[reducible]
def sketch.candidates.normalize.closure (F : Type _) :=
  sketch.shape.SketchShape F

/-- [bulksketch::sketch::candidates::normalize::{impl core::ops::function::Fn<(u64,), (usize, u64)> for bulksketch::sketch::candidates::normalize::{closure}<'_0, F>}::call]:
    Source: 'src/sketch/candidates.rs', lines 19:14-19:45 -/
def
  sketch.candidates.normalize.closure.Insts.CoreOpsFunctionFnTupleU64PairUsizeU64.call
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : sketch.candidates.normalize.closure F) (tupled_args : Std.U64) :
  Result (Std.Usize × Std.U64)
  := do
  let i ←
    sketch.shape.SketchShape.bucket_for fieldBinaryFieldInst c tupled_args
  ok (i, tupled_args)

/-- [bulksketch::sketch::candidates::normalize]: loop body 2:
    Source: 'src/sketch/candidates.rs', lines 28:12-36:13 -/
@[rust_loop_body]
def sketch.candidates.normalize_loop0_loop0_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (shape : sketch.shape.SketchShape F) (ids : Slice Std.U64)
  (middle : Std.Usize) («end» : Std.Usize)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (left : Std.Usize) (right : Std.Usize) :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64) ×
    Std.Usize × Std.Usize) ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some _ =>
    if left < middle
    then
      if right = «end»
      then
        let target ← Slice.index_usize ids left
        let left1 ← left + 1#usize
        ok (cont (iter1,
          fun im => let im1 := next_back im (some target)
                    back im1, left1, right))
      else
        let i ← Slice.index_usize ids left
        let p ←
          sketch.candidates.normalize.closure.Insts.CoreOpsFunctionFnTupleU64PairUsizeU64.call
            fieldBinaryFieldInst shape i
        let i1 ← Slice.index_usize ids right
        let p1 ←
          sketch.candidates.normalize.closure.Insts.CoreOpsFunctionFnTupleU64PairUsizeU64.call
            fieldBinaryFieldInst shape i1
        let b ←
          Pair.Insts.CoreCmpPartialOrdPair.le core.cmp.PartialOrdUsize
            core.cmp.PartialOrdU64 p p1
        if b
        then
          let left1 ← left + 1#usize
          ok (cont (iter1, fun im => let im1 := next_back im (some i)
                                     back im1, left1, right))
        else
          let right1 ← right + 1#usize
          ok (cont (iter1,
            fun im => let im1 := next_back im (some i1)
                      back im1, left, right1))
    else
      let target ← Slice.index_usize ids right
      let right1 ← right + 1#usize
      ok (cont (iter1,
        fun im => let im1 := next_back im (some target)
                  back im1, left, right1))

/-- [bulksketch::sketch::candidates::normalize]: loop 2:
    Source: 'src/sketch/candidates.rs', lines 28:12-36:13 -/
@[rust_loop]
def sketch.candidates.normalize_loop0_loop0_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (shape : sketch.shape.SketchShape F) (ids : Slice Std.U64)
  (middle : Std.Usize) («end» : Std.Usize) (left : Std.Usize)
  (right : Std.Usize) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1, left1, right1) =>
      sketch.candidates.normalize_loop0_loop0_loop0.body fieldBinaryFieldInst
      shape ids middle «end» iter1 back1 left1 right1)
    (iter, back, left, right)

/-- [bulksketch::sketch::candidates::normalize]: loop body 1:
    Source: 'src/sketch/candidates.rs', lines 24:8-38:9 -/
@[rust_loop_body]
def sketch.candidates.normalize_loop0_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (shape : sketch.shape.SketchShape F) (count : Std.Usize)
  (ids : Slice Std.U64) (width : Std.Usize) (temporary : Slice Std.U64)
  (start : Std.Usize) :
  Result (ControlFlow ((Slice Std.U64) × Std.Usize) (Slice Std.U64))
  := do
  if start < count
  then
    let i ← count - start
    let i1 ← lift (core.cmp.impls.OrdUsize.min width i)
    let middle ← start + i1
    let i2 ← count - middle
    let i3 ← lift (core.cmp.impls.OrdUsize.min width i2)
    let «end» ← middle + i3
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) temporary
        { start, «end» }
    let (iter, into_iter_back) ←
      MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter s
    let (im, back) ←
      sketch.candidates.normalize_loop0_loop0_loop0 fieldBinaryFieldInst iter
        (fun im1 => im1) shape ids middle «end» start middle
    let im1 := back im
    let s1 := into_iter_back im1
    let s2 := index_mut_back s1
    ok (cont (s2, «end»))
  else ok (done temporary)

/-- [bulksketch::sketch::candidates::normalize]: loop 1:
    Source: 'src/sketch/candidates.rs', lines 24:8-38:9 -/
@[rust_loop]
def sketch.candidates.normalize_loop0_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (shape : sketch.shape.SketchShape F) (count : Std.Usize)
  (ids : Slice Std.U64) (temporary : Slice Std.U64) (width : Std.Usize)
  (start : Std.Usize) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (temporary1, start1) => sketch.candidates.normalize_loop0_loop0.body
      fieldBinaryFieldInst shape count ids width temporary1 start1)
    (temporary, start)

/-- [bulksketch::sketch::candidates::normalize]: loop body 0:
    Source: 'src/sketch/candidates.rs', lines 22:4-45:5 -/
@[rust_loop_body]
def sketch.candidates.normalize_loop0.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (shape : sketch.shape.SketchShape F) (count : Std.Usize)
  (back : Slice Std.U64 → Slice Std.U64 → ((Slice Std.U64) × (Slice
  Std.U64))) (ids : Slice Std.U64) (temporary : Slice Std.U64)
  (width : Std.Usize) (flipped : Bool) :
  Result (ControlFlow ((Slice Std.U64 → Slice Std.U64 → ((Slice Std.U64) ×
    (Slice Std.U64))) × (Slice Std.U64) × (Slice Std.U64) × Std.Usize ×
    Bool) ((Slice Std.U64) × (Slice Std.U64) × Bool × (Slice Std.U64 →
    Slice Std.U64 → ((Slice Std.U64) × (Slice Std.U64)))))
  := do
  if width < count
  then
    let temporary1 ←
      sketch.candidates.normalize_loop0_loop0 fieldBinaryFieldInst shape count
        ids temporary width 0#usize
    let (ids1, temporary2, swap_back) := core.mem.swap ids temporary1
    let i ← count - width
    if width >= i
    then
      ok (done (ids1, temporary2, ¬ flipped,
        fun s s1 => let (s2, s3) := swap_back (s, s1)
                    back s2 s3))
    else
      let width1 ← width * 2#usize
      ok (cont (fun s s1 => let (s2, s3) := swap_back (s, s1)
                            back s2 s3, ids1, temporary2, width1, ¬ flipped))
  else ok (done (ids, temporary, flipped, back))

/-- [bulksketch::sketch::candidates::normalize]: loop 0:
    Source: 'src/sketch/candidates.rs', lines 22:4-45:5 -/
@[rust_loop]
def sketch.candidates.normalize_loop0
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (back : Slice Std.U64 → Slice Std.U64 → ((Slice Std.U64) × (Slice
  Std.U64))) (shape : sketch.shape.SketchShape F) (count : Std.Usize)
  (ids : Slice Std.U64) (temporary : Slice Std.U64) (width : Std.Usize)
  (flipped : Bool) :
  Result ((Slice Std.U64) × (Slice Std.U64) × Bool × (Slice Std.U64 →
    Slice Std.U64 → ((Slice Std.U64) × (Slice Std.U64))))
  := do
  loop
    (fun (back1, ids1, temporary1, width1, flipped1) =>
      sketch.candidates.normalize_loop0.body fieldBinaryFieldInst shape count
      back1 ids1 temporary1 width1 flipped1)
    (back, ids, temporary, width, flipped)

/-- [bulksketch::sketch::candidates::normalize]:
    Source: 'src/sketch/candidates.rs', lines 6:0-63:1 -/
def sketch.candidates.normalize
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (shape : sketch.shape.SketchShape F) (inputs : Slice Std.U64)
  (storage : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let b ← core.slice.Slice.is_empty inputs
  if b
  then core.slice.Slice.fill core.clone.CloneU64 storage 0#u64
  else
    let count := Slice.len inputs
    let i ← 2#usize * count
    let ((arrays, offsets), split_at_mut_back) ←
      core.slice.Slice.split_at_mut storage i
    let ((ids, temporary), split_at_mut_back1) ←
      core.slice.Slice.split_at_mut arrays count
    let ids1 ←
      core.slice.Slice.copy_from_slice core.marker.CopyU64 ids inputs
    let (ids2, temporary1, flipped, back) ←
      sketch.candidates.normalize_loop0 fieldBinaryFieldInst
        (fun s s1 => (s, s1)) shape count ids1 temporary 1#usize false
    let (ids3, temporary2, back1) ←
      if flipped
      then
        do
        let temporary3 ←
          core.slice.Slice.copy_from_slice core.marker.CopyU64 temporary1 ids2
        let (ids4, temporary4, swap_back) := core.mem.swap ids2 temporary3
        ok (ids4, temporary4, fun s s1 => swap_back (s, s1))
      else ok (ids2, temporary1, fun s s1 => (s, s1))
    let offsets1 ← core.slice.Slice.fill core.clone.CloneU64 offsets 0#u64
    let (offsets2, ids4) ←
      sketch.candidates.normalize_loop1 fieldBinaryFieldInst
        { start := 0#usize, «end» := count } shape offsets1 ids3 0#usize
    let i1 ← sketch.shape.SketchShape.bucket_count fieldBinaryFieldInst shape
    let offsets3 ←
      sketch.candidates.normalize_loop2 { start := 0#usize, «end» := i1 }
        offsets2
    let (s, s1) := back1 ids4 temporary2
    let arrays1 := split_at_mut_back1 (back s s1)
    ok (split_at_mut_back (arrays1, offsets3))

end bulksketch
