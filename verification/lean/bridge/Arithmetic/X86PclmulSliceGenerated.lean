-- Exact original PCLMUL slice declarations and scoped XMM/Zip models.
import Arithmetic.X86PclmulGenerated
import Arithmetic.MutableZipRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

local notation "core.core_arch.x86.__m128i" => X86PclmulRuntime.Xmm
local notation "core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128" => X86PclmulRuntime.clmul

/-- [bulksketch::backend::x86_pclmul::scale_xor]: loop body 0:
    Source: 'src/backend/x86_pclmul.rs', lines 183:8-185:9 -/
@[rust_loop_body]
def backend.x86_pclmul.scale_xor_loop0.body
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
    let (target, source) := p
    let target1 ← lift (target ^^^ source)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target1, source))
               back z1))

/-- [bulksketch::backend::x86_pclmul::scale_xor]: loop 0:
    Source: 'src/backend/x86_pclmul.rs', lines 183:8-185:9 -/
@[rust_loop]
def backend.x86_pclmul.scale_xor_loop0
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) => backend.x86_pclmul.scale_xor_loop0.body iter1 back1)
    (iter, back)

/-- [bulksketch::backend::x86_pclmul::scale_xor]: loop body 1:
    Source: 'src/backend/x86_pclmul.rs', lines 189:4-193:5 -/
@[rust_loop_body]
def backend.x86_pclmul.scale_xor_loop1.body
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (scale : core.core_arch.x86.__m128i)
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
    let (target, source) := p
    let mi ← backend.x86_pclmul.word source
    let product ←
      core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 mi scale
    let mi1 ← backend.x86_pclmul.reduced CL fieldBinaryFieldInst product
    let i ← backend.x86_pclmul.low mi1
    let target1 ← lift (target ^^^ i)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target1, source))
               back z1))

/-- [bulksketch::backend::x86_pclmul::scale_xor]: loop 1:
    Source: 'src/backend/x86_pclmul.rs', lines 189:4-193:5 -/
@[rust_loop]
def backend.x86_pclmul.scale_xor_loop1
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (scale : core.core_arch.x86.__m128i) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) => backend.x86_pclmul.scale_xor_loop1.body CL
      fieldBinaryFieldInst scale iter1 back1)
    (iter, back)

/-- [bulksketch::backend::x86_pclmul::scale_xor]:
    Source: 'src/backend/x86_pclmul.rs', lines 178:0-194:1 -/
def backend.x86_pclmul.scale_xor
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) (scale : Std.U64) :
  Result (Slice Std.U64)
  := do
  if scale = 0#u64
  then ok dst
  else
    if scale = 1#u64
    then
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut dst
      let (iter, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im src
      let back ← backend.x86_pclmul.scale_xor_loop0 iter (fun z => z)
      let im1 := trait_default_back back
      ok (iter_mut_back im1)
    else
      let scale1 ← backend.x86_pclmul.word scale
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut dst
      let (iter, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im src
      let back ←
        backend.x86_pclmul.scale_xor_loop1 CL fieldBinaryFieldInst iter
          (fun z => z) scale1
      let im1 := trait_default_back back
      ok (iter_mut_back im1)

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::scale_xor]:
    Source: 'src/backend/x86_pclmul.rs', lines 84:4-88:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.scale_xor
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) (scale : Std.U64) :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len src
  if left_val = right_val
  then backend.x86_pclmul.scale_xor true fieldBinaryFieldInst dst src scale
  else
    let _ ← core.fmt.Arguments.from_str (toStr "scale_xor length mismatch")
    fail panic

/-- [bulksketch::backend::x86_pclmul::square_slice]: loop body 0:
    Source: 'src/backend/x86_pclmul.rs', lines 198:4-203:5 -/
@[rust_loop_body]
def backend.x86_pclmul.square_slice_loop.body
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
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
    let (_, source) := p
    let source1 ← backend.x86_pclmul.word source
    let product ←
      core.core_arch.x86.pclmulqdq._mm_clmulepi64_si128 0#i32 source1 source1
    let mi ← backend.x86_pclmul.reduced CL fieldBinaryFieldInst product
    let target ← backend.x86_pclmul.low mi
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target, source))
               back z1))

/-- [bulksketch::backend::x86_pclmul::square_slice]: loop 0:
    Source: 'src/backend/x86_pclmul.rs', lines 198:4-203:5 -/
@[rust_loop]
def backend.x86_pclmul.square_slice_loop
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) => backend.x86_pclmul.square_slice_loop.body CL
      fieldBinaryFieldInst iter1 back1)
    (iter, back)

/-- [bulksketch::backend::x86_pclmul::square_slice]:
    Source: 'src/backend/x86_pclmul.rs', lines 197:0-204:1 -/
def backend.x86_pclmul.square_slice
  {F : Type _} (CL : Bool) (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut dst
  let (iter, trait_default_back) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
      Std.U64) im src
  let back ←
    backend.x86_pclmul.square_slice_loop CL fieldBinaryFieldInst iter
      (fun z => z)
  let im1 := trait_default_back back
  ok (iter_mut_back im1)

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::Arithmetic<F> for bulksketch::backend::x86_pclmul::Pclmul}::square_slice]:
    Source: 'src/backend/x86_pclmul.rs', lines 90:4-94:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractArithmetic.square_slice
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len src
  if left_val = right_val
  then backend.x86_pclmul.square_slice true fieldBinaryFieldInst dst src
  else
    let _ ←
      core.fmt.Arguments.from_str (toStr "square_slice length mismatch")
    fail panic

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_pclmul::Pclmul}::xor_assign]: loop body 0:
    Source: 'src/backend/x86_pclmul.rs', lines 105:8-107:9 -/
@[rust_loop_body]
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop.body
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
    let (target, source) := p
    let target1 ← lift (target ^^^ source)
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target1, source))
               back z1))

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_pclmul::Pclmul}::xor_assign]: loop 0:
    Source: 'src/backend/x86_pclmul.rs', lines 105:8-107:9 -/
@[rust_loop]
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) =>
      backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop.body
      iter1 back1)
    (iter, back)

/-- [bulksketch::backend::x86_pclmul::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_pclmul::Pclmul}::xor_assign]:
    Source: 'src/backend/x86_pclmul.rs', lines 103:4-108:5 -/
def
  backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (dst : Slice Std.U64) (src : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len dst
  let right_val := Slice.len src
  if left_val = right_val
  then
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut dst
    let (iter, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        Std.U64) (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
        Std.U64) im src
    let back ←
      backend.x86_pclmul.Pclmul.Insts.BulksketchBackendContractBulkKernels.xor_assign_loop
        iter (fun z => z)
    let im1 := trait_default_back back
    ok (iter_mut_back im1)
  else
    let _ ← core.fmt.Arguments.from_str (toStr "xor_assign length mismatch")
    fail panic

end bulksketch
