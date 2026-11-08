-- Exact original source declarations. Local notation binds the scoped std runtime.
module
public import Arithmetic.PortableHornerRuntime
public import Arithmetic.PortableGenerated
public import Arithmetic.PortableXorGenerated
public import Arithmetic.DenseNormalizationGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

local notation "core.slice.Slice.split_last" => Aeneas.Std.PortableHornerRuntime.splitLast
local notation "core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold" => Aeneas.Std.PortableHornerRuntime.reverseFold

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{closure}]
    Source: 'src/backend/portable.rs', lines 116:54-118:13 -/
@[reducible]
def backend.portable.BulkKernelsPortableF.horner_many.closure (F : Type _) :=
  Std.U64

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{impl core::ops::function::FnMut<(u64, &'_0 u64), u64> for bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{closure}<'_0, '_1, F>}::call_mut]:
    Source: 'src/backend/portable.rs', lines 116:54-118:13 -/
def
  backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.portable.BulkKernelsPortableF.horner_many.closure F)
  (tupled_args : (Std.U64 × Std.U64)) :
  Result (Std.U64 × (backend.portable.BulkKernelsPortableF.horner_many.closure
    F))
  := do
  let (value, coefficient) := tupled_args
  let i ←
    backend.portable.Portable.Insts.BulksketchBackendContractArithmetic.mul
      fieldBinaryFieldInst value c
  let i1 ← lift (i ^^^ coefficient)
  ok (i1, c)

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{impl core::ops::function::FnOnce<(u64, &'_0 u64), u64> for bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{closure}<'_0, '_1, F>}::call_once]:
    Source: 'src/backend/portable.rs', lines 116:54-118:13 -/
def
  backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64.call_once
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (c : backend.portable.BulkKernelsPortableF.horner_many.closure F)
  (p : (Std.U64 × Std.U64)) :
  Result Std.U64
  := do
  let (i, _) ←
    backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
      fieldBinaryFieldInst c p
  ok i

/-- Trait implementation: [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{impl core::ops::function::FnOnce<(u64, &'_0 u64), u64> for bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{closure}<'_0, '_1, F>}]
    Source: 'src/backend/portable.rs', lines 116:54-118:13 -/
@[reducible]
def
  backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnOnce
  (backend.portable.BulkKernelsPortableF.horner_many.closure F) (Std.U64 ×
  Std.U64) Std.U64 := {
  call_once :=
    backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64.call_once
    fieldBinaryFieldInst
}

/-- Trait implementation: [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{impl core::ops::function::FnMut<(u64, &'_0 u64), u64> for bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many::{closure}<'_0, '_1, F>}]
    Source: 'src/backend/portable.rs', lines 116:54-118:13 -/
@[reducible]
def
  backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) :
  core.ops.function.FnMut
  (backend.portable.BulkKernelsPortableF.horner_many.closure F) (Std.U64 ×
  Std.U64) Std.U64 := {
  FnOnceInst :=
    backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnOncePairU64Shared0U64U64
    fieldBinaryFieldInst
  call_mut :=
    backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64.call_mut
    fieldBinaryFieldInst
}

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many]: loop body 0:
    Source: 'src/backend/portable.rs', lines 115:8-119:9 -/
@[rust_loop_body]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many_loop.body
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F) (leading : Std.U64)
  (rest : Slice Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (_, point) := p
    let i ← core.slice.Slice.iter rest
    let r ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64)
        (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
        Std.U64) i
    let target ←
      core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.fold
        (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
        Std.U64)
        (backend.portable.BulkKernelsPortableF.horner_many.closure.Insts.CoreOpsFunctionFnMutPairU64Shared0U64U64
        fieldBinaryFieldInst) r leading point
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target, point))
               back z1))

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many]: loop 0:
    Source: 'src/backend/portable.rs', lines 115:8-119:9 -/
@[rust_loop]
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many_loop
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (leading : Std.U64) (rest : Slice Std.U64) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) =>
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many_loop.body
      fieldBinaryFieldInst leading rest iter1 back1)
    (iter, back)

/-- [bulksketch::backend::portable::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::portable::Portable}::horner_many]:
    Source: 'src/backend/portable.rs', lines 109:4-120:5 -/
def
  backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (coefficients : Slice Std.U64) (points : Slice Std.U64) (out : Slice Std.U64)
  :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len out
  let right_val := Slice.len points
  if left_val = right_val
  then
    let o ← core.slice.Slice.split_last coefficients
    match o with
    | none => core.slice.Slice.fill core.clone.CloneU64 out 0#u64
    | some p =>
      let (leading, rest) := p
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut out
      let (iter, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im points
      let back ←
        backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many_loop
          fieldBinaryFieldInst iter (fun z => z) leading rest
      let im1 := trait_default_back back
      ok (iter_mut_back im1)
  else
    let _ ← core.fmt.Arguments.from_str (toStr "horner_many length mismatch")
    fail panic

end bulksketch
