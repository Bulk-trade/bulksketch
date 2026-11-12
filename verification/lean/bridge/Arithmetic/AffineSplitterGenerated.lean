-- Exact checked source projection. See extraction/affine-splitter for provenance.
import Arithmetic.AffineLinearEvalGenerated
import Arithmetic.DenseNormalizationGenerated
import Arithmetic.RootTraceGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

variable (squareModel : Aeneas.Std.RootTraceRuntime.ModularSquare)

local notation "poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into" => squareModel

/-- [bulksketch::decode::affine::splitter::{closure#1}]
    Source: 'src/decode/affine.rs', lines 296:19-296:28 -/
@[reducible]
def decode.affine.splitter.closure_1 (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::affine::splitter::{closure}]
    Source: 'src/decode/affine.rs', lines 295:19-295:30 -/
@[reducible]
def decode.affine.splitter.closure (F : Type _) (K : Type _) := Unit

/-- [bulksketch::decode::affine::splitter::{impl core::ops::function::FnOnce<(usize,), usize> for bulksketch::decode::affine::splitter::{closure#1}<F, K>}::call_once]:
    Source: 'src/decode/affine.rs', lines 296:19-296:28 -/
def
  decode.affine.splitter.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.affine.splitter.closure_1 F K) (tupled_args : Std.Usize) :
  Result Std.Usize
  := do
  tupled_args + 1#usize

/-- Trait implementation: [bulksketch::decode::affine::splitter::{impl core::ops::function::FnOnce<(usize,), usize> for bulksketch::decode::affine::splitter::{closure#1}<F, K>}]
    Source: 'src/decode/affine.rs', lines 296:19-296:28 -/
@[reducible]
def decode.affine.splitter.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.affine.splitter.closure_1 F K) Std.Usize
  Std.Usize := {
  call_once :=
    decode.affine.splitter.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::affine::splitter::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::affine::splitter::{closure}<'_0, F, K>}::call_mut]:
    Source: 'src/decode/affine.rs', lines 295:19-295:30 -/
def
  decode.affine.splitter.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.affine.splitter.closure F K) (tupled_args : Std.U64) :
  Result (Bool × (decode.affine.splitter.closure F K))
  := do
  ok (tupled_args != 0#u64, ())

/-- [bulksketch::decode::affine::splitter::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::affine::splitter::{closure}<'_0, F, K>}::call_once]:
    Source: 'src/decode/affine.rs', lines 295:19-295:30 -/
def
  decode.affine.splitter.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.affine.splitter.closure F K) (i : Std.U64) :
  Result Bool
  := do
  let (b, _) ←
    decode.affine.splitter.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst () i
  ok b

/-- Trait implementation: [bulksketch::decode::affine::splitter::{impl core::ops::function::FnOnce<(&'_0 u64,), bool> for bulksketch::decode::affine::splitter::{closure}<'_0, F, K>}]
    Source: 'src/decode/affine.rs', lines 295:19-295:30 -/
@[reducible]
def
  decode.affine.splitter.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.affine.splitter.closure F K) Std.U64 Bool
  := {
  call_once :=
    decode.affine.splitter.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::affine::splitter::{impl core::ops::function::FnMut<(&'_0 u64,), bool> for bulksketch::decode::affine::splitter::{closure}<'_0, F, K>}]
    Source: 'src/decode/affine.rs', lines 295:19-295:30 -/
@[reducible]
def
  decode.affine.splitter.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.affine.splitter.closure F K) Std.U64 Bool
  := {
  FnOnceInst :=
    decode.affine.splitter.closure.Insts.CoreOpsFunctionFnOnceTupleShared0U64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.affine.splitter.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::affine::splitter]: loop body 0:
    Source: 'src/decode/affine.rs', lines 286:4-292:5 -/
@[rust_loop_body]
def decode.affine.splitter_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (polynomial : Slice Std.U64) (table : Slice Std.U64) (linear : Slice Std.U64)
  (d : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (output : Slice Std.U64) (raw : Slice types.RawProduct)
  (residue : Slice Std.U64) (squared : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice Std.U64) × (Slice
    types.RawProduct) × (Slice Std.U64) × (Slice Std.U64)) ((Slice Std.U64)
    × (Slice types.RawProduct) × (Slice Std.U64) × (Slice Std.U64)))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (output, raw, residue, squared))
  | some p =>
    let (i, coefficient) := p
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) output
        { «end» := d }
    let s1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.scale_xor s residue
        coefficient
    let i1 ← i + 1#usize
    let i2 := Slice.len linear
    if i1 != i2
    then
      let (_, squared1, raw1) ←
        poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
          fieldBinaryFieldInst backendcontractBulkKernelsInst residue
          polynomial table squared raw
      let residue1 ←
        core.slice.Slice.copy_from_slice core.marker.CopyU64 residue squared1
      let output1 := index_mut_back s1
      ok (cont (iter1, output1, raw1, residue1, squared1))
    else
      let output1 := index_mut_back s1
      ok (cont (iter1, output1, raw, residue, squared))

local notation "decode.affine.splitter_loop.body" => (decode.affine.splitter_loop.body squareModel)

/-- [bulksketch::decode::affine::splitter]: loop 0:
    Source: 'src/decode/affine.rs', lines 286:4-292:5 -/
@[rust_loop]
def decode.affine.splitter_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (polynomial : Slice Std.U64) (table : Slice Std.U64)
  (linear : Slice Std.U64) (output : Slice Std.U64)
  (raw : Slice types.RawProduct) (d : Std.Usize) (residue : Slice Std.U64)
  (squared : Slice Std.U64) :
  Result ((Slice Std.U64) × (Slice types.RawProduct) × (Slice Std.U64) ×
    (Slice Std.U64))
  := do
  loop
    (fun (iter1, output1, raw1, residue1, squared1) =>
      decode.affine.splitter_loop.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst polynomial table linear d iter1 output1
      raw1 residue1 squared1)
    (iter, output, raw, residue, squared)

local notation "decode.affine.splitter_loop" => (decode.affine.splitter_loop squareModel)

/-- [bulksketch::decode::affine::splitter]:
    Source: 'src/decode/affine.rs', lines 270:0-297:1 -/
def decode.affine.splitter
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (polynomial : Slice Std.U64) (table : Slice Std.U64) (linear : Slice Std.U64)
  (base : Std.U64) (output : Slice Std.U64) (work : Slice Std.U64)
  (raw : Slice types.RawProduct) :
  Result (Std.Usize × (Slice Std.U64) × (Slice Std.U64) × (Slice
    types.RawProduct))
  := do
  let i := Slice.len polynomial
  let d ← i - 1#usize
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) output
      { «end» := d }
  let s1 ← core.slice.Slice.fill core.clone.CloneU64 s 0#u64
  let i1 ←
    decode.affine.linear_eval fieldBinaryFieldInst
      backendcontractBulkKernelsInst linear base
  let output1 := index_mut_back s1
  let s2 ← Slice.update output1 0#usize i1
  let ((residue, rest), split_at_mut_back) ←
    core.slice.Slice.split_at_mut work d
  let (squared, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
      { «end» := d }
  let residue1 ← core.slice.Slice.fill core.clone.CloneU64 residue 0#u64
  let s3 ← Slice.update residue1 1#usize 1#u64
  let i2 ← core.slice.Slice.iter linear
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i2
  let (output2, raw1, residue2, squared1) ←
    decode.affine.splitter_loop fieldBinaryFieldInst
      backendcontractBulkKernelsInst iter polynomial table linear s2 raw d s3
      squared
  let s4 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) output2 { «end» := d }
  let i3 ← core.slice.Slice.iter s4
  let (o, _) ←
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.rposition
      (decode.affine.splitter.closure.Insts.CoreOpsFunctionFnMutTupleShared0U64Bool
      fieldBinaryFieldInst backendcontractBulkKernelsInst)
      (core.slice.iter.Iter.Insts.CoreIterTraitsExact_sizeExactSizeIteratorSharedT
      Std.U64)
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      Std.U64) i3 ()
  let i4 ←
    core.option.Option.map_or
      (decode.affine.splitter.closure_1.Insts.CoreOpsFunctionFnOnceTupleUsizeUsize
      fieldBinaryFieldInst backendcontractBulkKernelsInst) o 0#usize ()
  let rest1 := index_mut_back1 squared1
  let work1 := split_at_mut_back (residue2, rest1)
  ok (i4, output2, work1, raw1)
end bulksketch
