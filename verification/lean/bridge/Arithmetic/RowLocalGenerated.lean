-- Exact original checked row-local normalization declarations.
import Arithmetic.CandidateCompactGenerated
import Arithmetic.DegreeProbeRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace Aeneas.Std.CandidateRowsRuntime

structure Mapped (Iterator Closure : Type) where
  iterator : Iterator
  closure : Closure

def mapNew {I A B C : Type} (_ : core.iter.traits.iterator.Iterator I A)
    (_ : core.ops.function.FnMut C A B) (iterator : I) (closure : C) : Result (Mapped I C) :=
  .ok ⟨iterator, closure⟩

def mapNext {I A B C : Type} (source : core.iter.traits.iterator.Iterator I A)
    (callback : core.ops.function.FnMut C A B) (state : Mapped I C) :
    Result (Option B × Mapped I C) := do
  let (item, advanced) ← source.next state.iterator
  match item with
  | none => .ok (none, { state with iterator := advanced })
  | some value =>
    let (mapped, closure) ← callback.call_mut state.closure value
    .ok (some mapped, ⟨advanced, closure⟩)

def mapIterator {I A B C : Type} (source : core.iter.traits.iterator.Iterator I A)
    (callback : core.ops.function.FnMut C A B) :
    core.iter.traits.iterator.Iterator (Mapped I C) B where
  next := mapNext source callback

def sumBody {I : Type} (iterator : core.iter.traits.iterator.Iterator I Usize)
    (state : I × Usize) : Result (ControlFlow (I × Usize) Usize) := do
  let (item, advanced) ← iterator.next state.1
  match item with
  | none => .ok (.done state.2)
  | some word =>
    let count ← state.2 + word
    .ok (.cont (advanced, count))

def sumUsize {I : Type} (iterator : core.iter.traits.iterator.Iterator I Usize) (_ : Unit)
    (state : I) : Result Usize :=
  loop (sumBody iterator) (state, 0#usize)

end Aeneas.Std.CandidateRowsRuntime

namespace bulksketch

-- This body only reads DecodeRow.candidates. The other fields retain
-- value shape and have no executed Arc or OnceLock operations here.
local notation "alloc.sync.Arc" => Id
local notation "std.sync.once_lock.OnceLock" => Option
local notation "core.iter.traits.iterator.Iterator.map.default" => CandidateRowsRuntime.mapNew
local notation "core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator" => CandidateRowsRuntime.mapIterator
local notation "core.iter.traits.iterator.Iterator.sum.default" => CandidateRowsRuntime.sumUsize
local notation "Usize.Insts.CoreIterTraitsAccumSumUsize" => ()
local notation "core.slice.Slice.sort_unstable" =>
  (fun (_ : core.cmp.Ord U64) => DegreeProbeRuntime.sortUnsigned)

/-- [bulksketch::sketch::state::State]
    Source: 'src/sketch/state.rs', lines 23:0-28:1 -/
structure sketch.state.State (F : Type _) where
  shape : alloc.sync.Arc (sketch.shape.SketchShape F)
  words : alloc.vec.Vec Std.U64
  zero_words : alloc.vec.Vec Std.U64
  encoded_v1 : std.sync.once_lock.OnceLock (alloc.sync.Arc (Slice Std.U8))

/-- [bulksketch::sketch::state::FrozenSketch]
    Source: 'src/sketch/state.rs', lines 143:0-145:1
    Visibility: public -/
structure sketch.state.FrozenSketch (F : Type _) where
  state : alloc.sync.Arc (sketch.state.State F)

/-- [bulksketch::sketch::input::DecodeRow]
    Source: 'src/sketch/input.rs', lines 19:0-26:1
    Visibility: public -/
structure sketch.input.DecodeRow (F : Type _) where
  «local» : sketch.state.FrozenSketch F
  remote : Slice Std.U8
  candidates : Slice Std.U64

/-- [bulksketch::sketch::candidates::normalize_rows::{closure}]
    Source: 'src/sketch/candidates.rs', lines 80:39-80:65 -/
@[reducible]
def sketch.candidates.normalize_rows.closure (F : Type _) := Unit

/-- [bulksketch::sketch::candidates::normalize_rows::{impl core::ops::function::FnMut<(&'_0 bulksketch::sketch::input::DecodeRow<'_1, F>,), usize> for bulksketch::sketch::candidates::normalize_rows::{closure}<'_0, '_1, F>}::call_mut]:
    Source: 'src/sketch/candidates.rs', lines 80:39-80:65 -/
def
  sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize.call_mut
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : sketch.candidates.normalize_rows.closure F)
  (tupled_args : sketch.input.DecodeRow F) :
  Result (Std.Usize × (sketch.candidates.normalize_rows.closure F))
  := do
  let i := Slice.len tupled_args.candidates
  ok (i, ())

/-- [bulksketch::sketch::candidates::normalize_rows::{impl core::ops::function::FnOnce<(&'_0 bulksketch::sketch::input::DecodeRow<'_1, F>,), usize> for bulksketch::sketch::candidates::normalize_rows::{closure}<'_0, '_1, F>}::call_once]:
    Source: 'src/sketch/candidates.rs', lines 80:39-80:65 -/
def
  sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnOnceTupleShared0DecodeRowUsize.call_once
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : sketch.candidates.normalize_rows.closure F)
  (dr : sketch.input.DecodeRow F) :
  Result Std.Usize
  := do
  let (i, _) ←
    sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize.call_mut
      fieldBinaryFieldInst () dr
  ok i

/-- Trait implementation: [bulksketch::sketch::candidates::normalize_rows::{impl core::ops::function::FnOnce<(&'_0 bulksketch::sketch::input::DecodeRow<'_1, F>,), usize> for bulksketch::sketch::candidates::normalize_rows::{closure}<'_0, '_1, F>}]
    Source: 'src/sketch/candidates.rs', lines 80:39-80:65 -/
@[reducible]
def
  sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnOnceTupleShared0DecodeRowUsize
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnOnce (sketch.candidates.normalize_rows.closure F)
  (sketch.input.DecodeRow F) Std.Usize := {
  call_once :=
    sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnOnceTupleShared0DecodeRowUsize.call_once
    fieldBinaryFieldInst
}

/-- Trait implementation: [bulksketch::sketch::candidates::normalize_rows::{impl core::ops::function::FnMut<(&'_0 bulksketch::sketch::input::DecodeRow<'_1, F>,), usize> for bulksketch::sketch::candidates::normalize_rows::{closure}<'_0, '_1, F>}]
    Source: 'src/sketch/candidates.rs', lines 80:39-80:65 -/
@[reducible]
def
  sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnMut (sketch.candidates.normalize_rows.closure F)
  (sketch.input.DecodeRow F) Std.Usize := {
  FnOnceInst :=
    sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnOnceTupleShared0DecodeRowUsize
    fieldBinaryFieldInst
  call_mut :=
    sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize.call_mut
    fieldBinaryFieldInst
}

/-- [bulksketch::sketch::candidates::normalize_rows]: loop body 1:
    Source: 'src/sketch/candidates.rs', lines 93:8-99:9 -/
@[rust_loop_body]
def sketch.candidates.normalize_rows_loop0_loop0.body
  (start : Std.Usize) (iter : core.ops.range.Range Std.Usize)
  (ids : Slice Std.U64) (used : Std.Usize) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U64) ×
    Std.Usize) ((Slice Std.U64) × Std.Usize))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (ids, used))
  | some index =>
    let id ← Slice.index_usize ids index
    if id != 0#u64
    then
      if used = start
      then
        let s ← Slice.update ids used id
        let used1 ← used + 1#usize
        ok (cont (iter1, s, used1))
      else
        let i ← used - 1#usize
        let i1 ← Slice.index_usize ids i
        if i1 != id
        then
          let s ← Slice.update ids used id
          let used1 ← used + 1#usize
          ok (cont (iter1, s, used1))
        else ok (cont (iter1, ids, used))
    else ok (cont (iter1, ids, used))

/-- [bulksketch::sketch::candidates::normalize_rows]: loop 1:
    Source: 'src/sketch/candidates.rs', lines 93:8-99:9 -/
@[rust_loop]
def sketch.candidates.normalize_rows_loop0_loop0
  (iter : core.ops.range.Range Std.Usize) (ids : Slice Std.U64)
  (used : Std.Usize) (start : Std.Usize) :
  Result ((Slice Std.U64) × Std.Usize)
  := do
  loop
    (fun (iter1, ids1, used1) =>
      sketch.candidates.normalize_rows_loop0_loop0.body start iter1 ids1 used1)
    (iter, ids, used)

/-- [bulksketch::sketch::candidates::normalize_rows]: loop body 0:
    Source: 'src/sketch/candidates.rs', lines 89:4-101:5 -/
@[rust_loop_body]
def sketch.candidates.normalize_rows_loop0.body
  {F : Type _}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  (sketch.input.DecodeRow F))) (offsets : Slice Std.U64) (ids : Slice Std.U64)
  (used : Std.Usize) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter (sketch.input.DecodeRow F))) × (Slice Std.U64) ×
    (Slice Std.U64) × Std.Usize) ((Slice Std.U64) × (Slice Std.U64)))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter (sketch.input.DecodeRow F))
      iter
  match o with
  | none => ok (done (offsets, ids))
  | some p =>
    let (bucket, dr) := p
    let i := Slice.len dr.candidates
    let i1 ← used + i
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) ids
        { start := used, «end» := i1 }
    let s1 ←
      core.slice.Slice.copy_from_slice core.marker.CopyU64 s dr.candidates
    let ids1 := index_mut_back s1
    let i2 := Slice.len dr.candidates
    let i3 ← used + i2
    let (s2, index_mut_back1) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) ids1
        { start := used, «end» := i3 }
    let s3 ← core.slice.Slice.sort_unstable core.cmp.OrdU64 s2
    let i4 := Slice.len dr.candidates
    let i5 ← used + i4
    let ids2 := index_mut_back1 s3
    let (ids3, used1) ←
      sketch.candidates.normalize_rows_loop0_loop0
        { start := used, «end» := i5 } ids2 used used
    let i6 ← bucket + 1#usize
    let i7 ← lift (UScalar.cast .U64 used1)
    let s4 ← Slice.update offsets i6 i7
    ok (cont (iter1, s4, ids3, used1))

/-- [bulksketch::sketch::candidates::normalize_rows]: loop 0:
    Source: 'src/sketch/candidates.rs', lines 89:4-101:5 -/
@[rust_loop]
def sketch.candidates.normalize_rows_loop0
  {F : Type _}
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  (sketch.input.DecodeRow F))) (offsets : Slice Std.U64) (ids : Slice Std.U64)
  (used : Std.Usize) :
  Result ((Slice Std.U64) × (Slice Std.U64))
  := do
  loop
    (fun (iter1, offsets1, ids1, used1) =>
      sketch.candidates.normalize_rows_loop0.body iter1 offsets1 ids1 used1)
    (iter, offsets, ids, used)

/-- [bulksketch::sketch::candidates::normalize_rows]:
    Source: 'src/sketch/candidates.rs', lines 76:0-102:1 -/
def sketch.candidates.normalize_rows
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (rows : Slice (sketch.input.DecodeRow F)) (storage : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let i ← core.slice.Slice.iter rows
  let m ←
    core.iter.traits.iterator.Iterator.map.default
      (core.iter.traits.iterator.IteratorSliceIter (sketch.input.DecodeRow F))
      (sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize
      fieldBinaryFieldInst) i ()
  let count ←
    core.iter.traits.iterator.Iterator.sum.default
      (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
      (core.iter.traits.iterator.IteratorSliceIter (sketch.input.DecodeRow F))
      (sketch.candidates.normalize_rows.closure.Insts.CoreOpsFunctionFnMutTupleShared0DecodeRowUsize
      fieldBinaryFieldInst)) Usize.Insts.CoreIterTraitsAccumSumUsize m
  if count = 0#usize
  then core.slice.Slice.fill core.clone.CloneU64 storage 0#u64
  else
    let i1 ← 2#usize * count
    let ((arrays, offsets), split_at_mut_back) ←
      core.slice.Slice.split_at_mut storage i1
    let ((ids, s), split_at_mut_back1) ←
      core.slice.Slice.split_at_mut arrays count
    let offsets1 ← core.slice.Slice.fill core.clone.CloneU64 offsets 0#u64
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter (sketch.input.DecodeRow
        F)) i
    let (offsets2, ids1) ←
      sketch.candidates.normalize_rows_loop0 iter offsets1 ids 0#usize
    let arrays1 := split_at_mut_back1 (ids1, s)
    ok (split_at_mut_back (arrays1, offsets2))

end bulksketch
