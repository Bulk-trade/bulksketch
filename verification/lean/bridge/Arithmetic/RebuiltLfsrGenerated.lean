-- Exact original source declarations with scoped standard-library bindings.
module
public import Arithmetic.RebuiltLfsrRuntime
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive
local notation "Mut1A.Insts.CoreCmpPartialEqShared0B.ne" => RebuiltLfsrRuntime.mutableSharedNe
local notation "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter" =>
  RebuiltLfsrRuntime.mutableIntoIter

/-- Trait implementation: [core::slice::cmp::{impl core::cmp::PartialEq<[U]> for [T]}]
    Source: '/rustc/library/core/src/slice/cmp.rs', lines 14:0-16:28
    Name pattern: [core::cmp::PartialEq<[@T], [@U]>] -/
@[reducible, rust_trait_impl "core::cmp::PartialEq<[@T], [@U]>"]
impl_def Slice.Insts.CoreCmpPartialEqSlice {T : Type _} {U : Type _}
  (cmpPartialEqInst : core.cmp.PartialEq T U) : core.cmp.PartialEq (Slice T)
  (Slice U) := {
  eq := core.slice.cmp.PartialEqSlice.eq cmpPartialEqInst
  ne := core.cmp.PartialEq.ne.trait_default (Slice.Insts.CoreCmpPartialEqSlice
    cmpPartialEqInst)
}

/-- [bulksketch::decode::verify::rebuilt_lfsr]: loop body 0:
    Source: 'src/decode/verify.rs', lines 86:4-88:5 -/
@[rust_loop_body]
def decode.verify.rebuilt_lfsr_loop0.body
  {F : Type _} {K : Type _} (backendcontractBulkKernelsInst :
  backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (coefficients : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done coefficients)
  | some p =>
    let (index, root) := p
    let i ← index + 2#usize
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) coefficients
        { «end» := i }
    let s1 ← backendcontractBulkKernelsInst.multiply_linear s root
    let coefficients1 := index_mut_back s1
    ok (cont (iter1, coefficients1))

/-- [bulksketch::decode::verify::rebuilt_lfsr]: loop 0:
    Source: 'src/decode/verify.rs', lines 86:4-88:5 -/
@[rust_loop]
def decode.verify.rebuilt_lfsr_loop0
  {F : Type _} {K : Type _} (backendcontractBulkKernelsInst :
  backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (coefficients : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, coefficients1) => decode.verify.rebuilt_lfsr_loop0.body
      backendcontractBulkKernelsInst iter1 coefficients1)
    (iter, coefficients)

/-- [bulksketch::decode::verify::rebuilt_lfsr]: loop body 1:
    Source: 'src/decode/verify.rs', lines 95:4-97:5 -/
@[rust_loop_body]
def decode.verify.rebuilt_lfsr_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64))
    ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64 →
    core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some coefficient =>
    let coefficient1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.square coefficient
    ok (cont (iter1,
      fun im => let im1 := next_back im (some coefficient1)
                back im1))

/-- [bulksketch::decode::verify::rebuilt_lfsr]: loop 1:
    Source: 'src/decode/verify.rs', lines 95:4-97:5 -/
@[rust_loop]
def decode.verify.rebuilt_lfsr_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => decode.verify.rebuilt_lfsr_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

/-- [bulksketch::decode::verify::rebuilt_lfsr]:
    Source: 'src/decode/verify.rs', lines 75:0-99:1 -/
def decode.verify.rebuilt_lfsr
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (roots : Slice Std.U64) (odd : Slice Std.U64) (coefficients : Slice Std.U64)
  (expected : Slice Std.U64) :
  Result (Bool × (Slice Std.U64) × (Slice Std.U64))
  := do
  let degree := Slice.len roots
  let i := Slice.len odd
  let «prefix» ← lift (core.cmp.impls.OrdUsize.min degree i)
  let (coefficients1, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
      Std.U64) coefficients { «end» := degree }
  let coefficients2 ←
    core.slice.Slice.fill core.clone.CloneU64 coefficients1 0#u64
  let s ← Slice.update coefficients2 0#usize 1#u64
  let i1 ← core.slice.Slice.iter roots
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i1
  let coefficients3 ←
    decode.verify.rebuilt_lfsr_loop0 backendcontractBulkKernelsInst iter s
  let (expected1, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) expected
      { «end» := «prefix» }
  let expected2 ← core.slice.Slice.fill core.clone.CloneU64 expected1 0#u64
  let expected3 ←
    backendcontractBulkKernelsInst.insert_nonzero expected2 roots
  let s1 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) odd { «end» := «prefix» }
  let b ←
    Mut1A.Insts.CoreCmpPartialEqShared0B.ne (Slice.Insts.CoreCmpPartialEqSlice
      core.cmp.PartialEqU64) expected3 s1
  if b
  then
    let coefficients4 := index_mut_back coefficients3
    let expected4 := index_mut_back1 expected3
    ok (false, coefficients4, expected4)
  else
    let (s2, index_mut_back2) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) coefficients3
        { start := 1#usize }
    let (iter1, into_iter_back) ←
      MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        s2
    let (im, back) ←
      decode.verify.rebuilt_lfsr_loop1 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter1 (fun im1 => im1)
    let im1 := back im
    let s3 := into_iter_back im1
    let coefficients4 := index_mut_back2 s3
    let b1 ←
      backendcontractBulkKernelsInst.odd_recurrence_matches odd coefficients4
    let coefficients5 := index_mut_back coefficients4
    let expected4 := index_mut_back1 expected3
    ok (b1, coefficients5, expected4)

end bulksketch
