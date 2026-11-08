-- Exact original PCLMUL Horner declarations and scoped XMM/Zip models.
import Arithmetic.X86PclmulGenerated
import Arithmetic.MutableZipRuntime
import Arithmetic.DenseNormalizationGenerated
import Arithmetic.PortableHornerRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

local notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm
local notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul
local notation "core.core_arch.x86.sse2._mm_xor_si128" => X86PclmulRuntime.xor
local notation "core.slice.Slice.split_last" => PortableHornerRuntime.splitLast

/-- [bulksketch::backend::x86_pclmul::horner]: loop body 1:
    Source: 'src/backend/x86_pclmul.rs', lines 238:8-242:9 -/
@[rust_loop_body]
def backend.x86_pclmul.horner_loop0_loop0.body
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (point : core.core_arch.x86.__m128i)
  (iter : core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))
  (value : core.core_arch.x86.__m128i) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.slice.iter.Iter
    Std.U64)) × core.core_arch.x86.__m128i) core.core_arch.x86.__m128i)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      Std.U64) iter
  match o with
  | none => ok (done value)
  | some coefficient =>
    let product ←
      core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 value point
    let mi ← backend.x86_pclmul.reduced CL fieldBinaryFieldInst product
    let mi1 ← backend.x86_pclmul.word coefficient
    let value1 ← core.core_arch.x86.sse2._mm_xor_si128 mi mi1
    ok (cont (iter1, value1))

/-- [bulksketch::backend::x86_pclmul::horner]: loop 1:
    Source: 'src/backend/x86_pclmul.rs', lines 238:8-242:9 -/
@[rust_loop]
def backend.x86_pclmul.horner_loop0_loop0
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))
  (point : core.core_arch.x86.__m128i) (value : core.core_arch.x86.__m128i) :
  Result core.core_arch.x86.__m128i
  := do
  loop
    (fun (iter1, value1) => backend.x86_pclmul.horner_loop0_loop0.body CL
      fieldBinaryFieldInst point iter1 value1)
    (iter, value)

/-- [bulksketch::backend::x86_pclmul::horner]: loop body 0:
    Source: 'src/backend/x86_pclmul.rs', lines 235:4-244:5 -/
@[rust_loop_body]
def backend.x86_pclmul.horner_loop0.body
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (leading : Std.U64) (rest : Slice Std.U64)
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
    let point1 ← backend.x86_pclmul.word point
    let value ← backend.x86_pclmul.word leading
    let i ← core.slice.Slice.iter rest
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64)
        (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
        Std.U64) i
    let value1 ←
      backend.x86_pclmul.horner_loop0_loop0 CL fieldBinaryFieldInst iter2
        point1 value
    let target ← backend.x86_pclmul.low value1
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target, point))
               back z1))

/-- [bulksketch::backend::x86_pclmul::horner]: loop 0:
    Source: 'src/backend/x86_pclmul.rs', lines 235:4-244:5 -/
@[rust_loop]
def backend.x86_pclmul.horner_loop0
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
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
    (fun (iter1, back1) => backend.x86_pclmul.horner_loop0.body CL
      fieldBinaryFieldInst leading rest iter1 back1)
    (iter, back)

/-- [bulksketch::backend::x86_pclmul::horner]:
    Source: 'src/backend/x86_pclmul.rs', lines 226:0-245:1 -/
def backend.x86_pclmul.horner
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (coefficients : Slice Std.U64) (points : Slice Std.U64) (out : Slice Std.U64)
  :
  Result (Slice Std.U64)
  := do
  let o ← core.slice.Slice.split_last coefficients
  match o with
  | none => core.slice.Slice.fill core.clone.CloneU64 out 0#u64
  | some p =>
    let (leading, rest) := p
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut out
    let (iter, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        Std.U64) (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
        Std.U64) im points
    let back ←
      backend.x86_pclmul.horner_loop0 CL fieldBinaryFieldInst iter (fun z => z)
        leading rest
    let im1 := trait_default_back back
    ok (iter_mut_back im1)

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_pclmul::Pclmul}::horner_many]:
    Source: 'src/backend/x86_pclmul.rs', lines 110:4-114:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.horner_many
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (coefficients : Slice Std.U64) (points : Slice Std.U64) (out : Slice Std.U64)
  :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len out
  let right_val := Slice.len points
  if left_val = right_val
  then
    backend.x86_pclmul.horner true fieldBinaryFieldInst coefficients points out
  else
    let _ ← core.fmt.Arguments.from_str (toStr "horner_many length mismatch")
    fail panic

end bulksketch
