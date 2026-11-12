-- Exact original-source declaration projection. Imports and scoped external bindings are adapted only.
module
public import Arithmetic.RebuiltLfsrGenerated
public import Arithmetic.CertificateRuntime
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.iter.traits.iterator.Iterator.any.default" => Aeneas.Std.CertificateRuntime.any
local notation "Mut1A.Insts.CoreCmpPartialEqShared0B.eq" => Aeneas.Std.CertificateRuntime.mutableSharedEq

/-- [bulksketch::decode::deg34::certificate::{closure}]
    Source: 'src/decode/deg34.rs', lines 121:17-121:81 -/
@[reducible]
def decode.deg34.certificate.closure (F : Type _) (K : Type _) := Slice Std.U64

/-- Trait implementation: [core::iter::range::{impl core::iter::traits::double_ended::DoubleEndedIterator<A> for core::ops::range::RangeInclusive<A>}]
    Source: '/rustc/library/core/src/iter/range.rs', lines 1626:0-1626:60
    Name pattern: [core::iter::traits::double_ended::DoubleEndedIterator<core::ops::range::RangeInclusive<@A>, @A>] -/
@[reducible, rust_trait_impl
  "core::iter::traits::double_ended::DoubleEndedIterator<core::ops::range::RangeInclusive<@A>, @A>"]
def
  core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
  {A : Type _} (StepInst : core.iter.range.Step A) :
  core.iter.traits.double_ended.DoubleEndedIterator
  (core.ops.range.RangeInclusive A) A := {
  iteratorInst :=
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator StepInst
  next_back :=
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsDoubleEndedIterator.next_back
    StepInst
}

/-- [bulksketch::decode::deg34::certificate::{impl core::ops::function::FnMut<((usize, &'_0 u64),), bool> for bulksketch::decode::deg34::certificate::{closure}<'_0, '_1, F, K>}::call_mut]:
    Source: 'src/decode/deg34.rs', lines 121:17-121:81 -/
def
  decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool.call_mut
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.deg34.certificate.closure F K)
  (tupled_args : (Std.Usize × Std.U64)) :
  Result (Bool × (decode.deg34.certificate.closure F K))
  := do
  let (i, x) := tupled_args
  if x = 0#u64
  then ok (true, c)
  else
    let i1 ← fieldBinaryFieldInst.MASK
    let i2 ← lift (~~~ i1)
    let i3 ← lift (x &&& i2)
    if i3 != 0#u64
    then ok (true, c)
    else
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) c
          { «end» := i }
      let b ← core.slice.Slice.contains core.cmp.PartialEqU64 s x
      ok (b, c)

/-- [bulksketch::decode::deg34::certificate::{impl core::ops::function::FnOnce<((usize, &'_0 u64),), bool> for bulksketch::decode::deg34::certificate::{closure}<'_0, '_1, F, K>}::call_once]:
    Source: 'src/decode/deg34.rs', lines 121:17-121:81 -/
def
  decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool.call_once
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (c : decode.deg34.certificate.closure F K) (p : (Std.Usize × Std.U64)) :
  Result Bool
  := do
  let (b, _) ←
    decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool.call_mut
      fieldBinaryFieldInst backendcontractBulkKernelsInst c p
  ok b

/-- Trait implementation: [bulksketch::decode::deg34::certificate::{impl core::ops::function::FnOnce<((usize, &'_0 u64),), bool> for bulksketch::decode::deg34::certificate::{closure}<'_0, '_1, F, K>}]
    Source: 'src/decode/deg34.rs', lines 121:17-121:81 -/
@[reducible]
def
  decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnOnce (decode.deg34.certificate.closure F K) (Std.Usize ×
  Std.U64) Bool := {
  call_once :=
    decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool.call_once
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- Trait implementation: [bulksketch::decode::deg34::certificate::{impl core::ops::function::FnMut<((usize, &'_0 u64),), bool> for bulksketch::decode::deg34::certificate::{closure}<'_0, '_1, F, K>}]
    Source: 'src/decode/deg34.rs', lines 121:17-121:81 -/
@[reducible]
def
  decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F) :
  core.ops.function.FnMut (decode.deg34.certificate.closure F K) (Std.Usize ×
  Std.U64) Bool := {
  FnOnceInst :=
    decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnOnceTuplePairUsizeShared0U64Bool
    fieldBinaryFieldInst backendcontractBulkKernelsInst
  call_mut :=
    decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool.call_mut
    fieldBinaryFieldInst backendcontractBulkKernelsInst
}

/-- [bulksketch::decode::deg34::certificate]: loop body 1:
    Source: 'src/decode/deg34.rs', lines 130:8-132:9 -/
@[rust_loop_body]
def decode.deg34.certificate_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (root : Std.U64)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Std.Usize))
  (product : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev
    (core.ops.range.RangeInclusive Std.Usize)) × (Slice Std.U64)) (Slice
    Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done product)
  | some j =>
    let i ← j - 1#usize
    let i1 ← Slice.index_usize product i
    let i2 ← Slice.index_usize product j
    let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul root i2
    let i4 ← lift (i1 ^^^ i3)
    let s ← Slice.update product j i4
    ok (cont (iter1, s))

/-- [bulksketch::decode::deg34::certificate]: loop 1:
    Source: 'src/decode/deg34.rs', lines 130:8-132:9 -/
@[rust_loop]
def decode.deg34.certificate_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.RangeInclusive Std.Usize))
  (product : Slice Std.U64) (root : Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, product1) => decode.deg34.certificate_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst root iter1 product1)
    (iter, product)

/-- [bulksketch::decode::deg34::certificate]: loop body 0:
    Source: 'src/decode/deg34.rs', lines 128:4-134:5 -/
@[rust_loop_body]
def decode.deg34.certificate_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (product : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done product)
  | some p =>
    let (degree, root) := p
    let i ← Slice.index_usize product degree
    let i1 ← degree + 1#usize
    let s ← Slice.update product i1 i
    let ri ← core.ops.range.RangeInclusive.new 1#usize degree
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator
        core.iter.range.StepUsize)
        (core.ops.range.RangeInclusive.Insts.CoreIterTraitsDouble_endedDoubleEndedIterator
        core.iter.range.StepUsize) ri
    let product1 ←
      decode.deg34.certificate_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter2 s root
    let i2 ← Slice.index_usize product1 0#usize
    let i3 ← backendcontractBulkKernelsInst.ArithmeticInst.mul root i2
    let s1 ← Slice.update product1 0#usize i3
    ok (cont (iter1, s1))

/-- [bulksketch::decode::deg34::certificate]: loop 0:
    Source: 'src/decode/deg34.rs', lines 128:4-134:5 -/
@[rust_loop]
def decode.deg34.certificate_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (product : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, product1) => decode.deg34.certificate_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 product1)
    (iter, product)

/-- [bulksketch::decode::deg34::certificate]:
    Source: 'src/decode/deg34.rs', lines 112:0-136:1 -/
def decode.deg34.certificate
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (factor : Slice Std.U64) (roots : Slice Std.U64) (product : Slice Std.U64) :
  Result (Bool × (Slice Std.U64))
  := do
  let i := Slice.len roots
  let i1 ← i + 1#usize
  let i2 := Slice.len factor
  if i1 != i2
  then ok (false, product)
  else
    let i3 ← core.slice.Slice.iter roots
    let e ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64) i3
    let (b, _) ←
      core.iter.traits.iterator.Iterator.any.default
        (core.iter.traits.iterator.IteratorEnumerate
        (core.iter.traits.iterator.IteratorSliceIter Std.U64))
        (decode.deg34.certificate.closure.Insts.CoreOpsFunctionFnMutTuplePairUsizeShared0U64Bool
        fieldBinaryFieldInst backendcontractBulkKernelsInst) e roots
    if b
    then ok (false, product)
    else
      let i4 := Slice.len factor
      let (product1, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) product
          { «end» := i4 }
      let product2 ← core.slice.Slice.fill core.clone.CloneU64 product1 0#u64
      let s ← Slice.update product2 0#usize 1#u64
      let iter ←
        core.iter.traits.iterator.Iterator.enumerate.trait_default
          (core.iter.traits.iterator.IteratorSliceIter Std.U64) i3
      let product3 ←
        decode.deg34.certificate_loop0 fieldBinaryFieldInst
          backendcontractBulkKernelsInst iter s
      let b1 ←
        Mut1A.Insts.CoreCmpPartialEqShared0B.eq
          (Slice.Insts.CoreCmpPartialEqSlice core.cmp.PartialEqU64) product3
          factor
      let product4 := index_mut_back product3
      ok (b1, product4)

end bulksketch
