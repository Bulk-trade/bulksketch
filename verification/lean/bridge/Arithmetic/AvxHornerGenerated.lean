-- Exact declarations from the reviewed checked kernel and stock selector captures.
import Arithmetic.AvxHornerChunkRuntime
import Arithmetic.PortableHornerGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (loadModel : Aeneas.Std.AvxSquareRuntime.Load)
variable (storeModel : Aeneas.Std.AvxSquareRuntime.Store)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "core.slice.Slice.split_last" => PortableHornerRuntime.splitLast
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel
local notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.iter.ChunksMut" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks
local notation "core.slice.Slice.chunks_mut" => AvxHornerChunkRuntime.chunksMut
local notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice" =>
  (fun T => @AvxHornerChunkRuntime.nextShared T)
local notation "core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice" =>
  (fun T => @AvxHornerChunkRuntime.nextMutable T)
local notation "core.iter.traits.collect.IntoIterator.Blanket" => AvxHornerChunkRuntime.chunkBlanket
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" => AvxHornerChunkRuntime.zipConstruct
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  AvxHornerChunkRuntime.zipNext

/-- [bulksketch::backend::x86_vpclmul512::horner_kernel]: loop body 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 385:8-390:9 -/
@[rust_loop_body]
def backend.x86_vpclmul512.horner_kernel_loop0_loop0.body
  (CL : Bool) (points : core.core_arch.x86.__m512i)
  (iter : core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))
  (value : core.core_arch.x86.__m512i) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.slice.iter.Iter
    Std.U64)) × core.core_arch.x86.__m512i) core.core_arch.x86.__m512i)
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
      Std.U64) iter
  match o with
  | none => ok (done value)
  | some coefficient =>
    let mi ← backend.x86_vpclmul512.multiply CL value points
    let a ← core.num.U64.to_ne_bytes coefficient
    let i ← core.num.I64.from_ne_bytes a
    let mi1 ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
    let value1 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi mi1
    ok (cont (iter1, value1))

/-- [bulksketch::backend::x86_vpclmul512::horner_kernel]: loop 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 385:8-390:9 -/
@[rust_loop]
def backend.x86_vpclmul512.horner_kernel_loop0_loop0
  (CL : Bool)
  (iter : core.iter.adapters.rev.Rev (core.slice.iter.Iter Std.U64))
  (points : core.core_arch.x86.__m512i) (value : core.core_arch.x86.__m512i) :
  Result core.core_arch.x86.__m512i
  := do
  loop
    (fun (iter1, value1) =>
      backend.x86_vpclmul512.horner_kernel_loop0_loop0.body CL points iter1
      value1)
    (iter, value)

/-- [bulksketch::backend::x86_vpclmul512::horner_kernel]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 382:4-392:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.horner_kernel_loop0.body
  (CL : Bool) (leading : Std.U64) (rest : Slice Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
  (core.slice.iter.ChunksMut Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
  (core.slice.iter.ChunksMut Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.Chunks Std.U64) (core.slice.iter.ChunksMut Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.Chunks
    Std.U64) (core.slice.iter.ChunksMut Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
    (core.slice.iter.ChunksMut Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.Chunks Std.U64) (core.slice.iter.ChunksMut Std.U64)))
    (core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
    (core.slice.iter.ChunksMut Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U64)
      (core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
      Std.U64) iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (points, out) := p
    let points1 ← backend.x86_vpclmul512.load points
    let a ← core.num.U64.to_ne_bytes leading
    let i ← core.num.I64.from_ne_bytes a
    let value ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
    let i1 ← core.slice.Slice.iter rest
    let iter2 ←
      core.iter.traits.iterator.Iterator.rev.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64)
        (core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT
        Std.U64) i1
    let value1 ←
      backend.x86_vpclmul512.horner_kernel_loop0_loop0 CL iter2 points1 value
    let out1 ← backend.x86_vpclmul512.store out value1
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (points, out1))
               back z1))

local notation "backend.x86_vpclmul512.horner_kernel_loop0.body" => (backend.x86_vpclmul512.horner_kernel_loop0.body loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::horner_kernel]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 382:4-392:5 -/
@[rust_loop]
def backend.x86_vpclmul512.horner_kernel_loop0
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
  (core.slice.iter.ChunksMut Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
  (core.slice.iter.ChunksMut Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.Chunks Std.U64) (core.slice.iter.ChunksMut Std.U64))
  (leading : Std.U64) (rest : Slice Std.U64) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.Chunks Std.U64)
    (core.slice.iter.ChunksMut Std.U64))
  := do
  loop
    (fun (iter1, back1) => backend.x86_vpclmul512.horner_kernel_loop0.body CL
      leading rest iter1 back1)
    (iter, back)

local notation "backend.x86_vpclmul512.horner_kernel_loop0" => (backend.x86_vpclmul512.horner_kernel_loop0 loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::horner_kernel]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 377:0-393:1 -/
def backend.x86_vpclmul512.horner_kernel
  (CL : Bool) (coefficients : Slice Std.U64) (points : Slice Std.U64)
  (out : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let o ← core.slice.Slice.split_last coefficients
  match o with
  | none => core.slice.Slice.fill core.clone.CloneU64 out 0#u64
  | some p =>
    let (leading, rest) := p
    let c ← core.slice.Slice.chunks points 8#usize
    let (cm, chunks_mut_back) ← core.slice.Slice.chunks_mut out 8#usize
    let (iter, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
        Std.U64) (core.iter.traits.collect.IntoIterator.Blanket
        (core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
        Std.U64)) c cm
    let back ←
      backend.x86_vpclmul512.horner_kernel_loop0 CL iter (fun z => z) leading
        rest
    let cm1 := trait_default_back back
    ok (chunks_mut_back cm1)

local notation "backend.x86_vpclmul512.horner_kernel" => (backend.x86_vpclmul512.horner_kernel loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::horner_many]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 372:0-374:1 -/
def backend.x86_vpclmul512.horner_many
  (coefficients : Slice Std.U64) (points : Slice Std.U64) (out : Slice Std.U64)
  :
  Result (Slice Std.U64)
  := do
  backend.x86_vpclmul512.horner_kernel true coefficients points out

local notation "backend.x86_vpclmul512.horner_many" => (backend.x86_vpclmul512.horner_many loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::horner_many]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 180:4-187:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.horner_many
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (coefficients : Slice Std.U64) (points : Slice Std.U64) (out : Slice Std.U64)
  :
  Result (Slice Std.U64)
  := do
  let left_val := Slice.len out
  let right_val := Slice.len points
  if left_val = right_val
  then
    let i ← fieldBinaryFieldInst.BITS
    if i != 64#u32
    then
      backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.horner_many
        fieldBinaryFieldInst coefficients points out
    else backend.x86_vpclmul512.horner_many coefficients points out
  else
    let _ ← core.fmt.Arguments.from_str (toStr "horner_many length mismatch")
    fail panic

end bulksketch
