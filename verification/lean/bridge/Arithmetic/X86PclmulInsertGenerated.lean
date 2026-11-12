-- Original checked PCLMUL insertion and trait entry with exact register and slice bindings.
import Arithmetic.X86PclmulGenerated
import Arithmetic.PortableInsertionGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

local notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm
local notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul

/-- [bulksketch::backend::x86_pclmul::insert]: loop body 1:
    Source: 'src/backend/x86_pclmul.rs', lines 216:8-221:9 -/
@[rust_loop_body]
def backend.x86_pclmul.insert_loop0_loop0.body
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (square : core.core_arch.x86.__m128i)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (power : core.core_arch.x86.__m128i) :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64) ×
    core.core_arch.x86.__m128i) ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some syndrome =>
    let product ←
      core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 power square
    let power1 ← backend.x86_pclmul.reduced CL fieldBinaryFieldInst product
    let i ← backend.x86_pclmul.low power1
    let syndrome1 ← lift (syndrome ^^^ i)
    ok (cont (iter1,
      fun im => let im1 := next_back im (some syndrome1)
                back im1, power1))

/-- [bulksketch::backend::x86_pclmul::insert]: loop 1:
    Source: 'src/backend/x86_pclmul.rs', lines 216:8-221:9 -/
@[rust_loop]
def backend.x86_pclmul.insert_loop0_loop0
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (square : core.core_arch.x86.__m128i) (power : core.core_arch.x86.__m128i) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1, power1) => backend.x86_pclmul.insert_loop0_loop0.body
      CL fieldBinaryFieldInst square iter1 back1 power1)
    (iter, back, power)

/-- [bulksketch::backend::x86_pclmul::insert]: loop body 0:
    Source: 'src/backend/x86_pclmul.rs', lines 211:4-222:5 -/
@[rust_loop_body]
def backend.x86_pclmul.insert_loop0.body
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (first : Std.U64)
  (successors : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Iter Std.U64) × Std.U64 × (Slice
    Std.U64)) (Std.U64 × (Slice Std.U64)))
  := do
  let (o, iter1) ← core.slice.iter.IteratorSliceIter.next iter
  match o with
  | none => ok (done (first, successors))
  | some id =>
    let first1 ← lift (first ^^^ id)
    let i ← backend.x86_pclmul.multiply false fieldBinaryFieldInst id id
    let square ← backend.x86_pclmul.word i
    let power ← backend.x86_pclmul.word id
    let (iter2, into_iter_back) ←
      MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter
        successors
    let (im, back) ←
      backend.x86_pclmul.insert_loop0_loop0 CL fieldBinaryFieldInst iter2
        (fun im1 => im1) square power
    let im1 := back im
    let s := into_iter_back im1
    ok (cont (iter1, first1, s))

/-- [bulksketch::backend::x86_pclmul::insert]: loop 0:
    Source: 'src/backend/x86_pclmul.rs', lines 211:4-222:5 -/
@[rust_loop]
def backend.x86_pclmul.insert_loop0
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.slice.iter.Iter Std.U64) (first : Std.U64)
  (successors : Slice Std.U64) :
  Result (Std.U64 × (Slice Std.U64))
  := do
  loop
    (fun (iter1, first1, successors1) => backend.x86_pclmul.insert_loop0.body
      CL fieldBinaryFieldInst iter1 first1 successors1)
    (iter, first, successors)

/-- [bulksketch::backend::x86_pclmul::insert]:
    Source: 'src/backend/x86_pclmul.rs', lines 207:0-223:1 -/
def backend.x86_pclmul.insert
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let (o, split_first_mut_back) ← core.slice.Slice.split_first_mut odd
  match o with
  | none => ok (split_first_mut_back none)
  | some p =>
    let (first, successors) := p
    let iter ←
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter
        ids
    let (first1, successors1) ←
      backend.x86_pclmul.insert_loop0 CL fieldBinaryFieldInst iter first
        successors
    ok (split_first_mut_back (some (first1, successors1)))

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_pclmul::Pclmul}::insert_nonzero]:
    Source: 'src/backend/x86_pclmul.rs', lines 98:4-101:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  backend.x86_pclmul.insert true fieldBinaryFieldInst odd ids

end bulksketch
