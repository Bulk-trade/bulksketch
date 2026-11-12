-- Exact original AVX slice kernel declarations from checked stock extraction.
import Arithmetic.AvxSliceKernelRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (loadModel : AvxSquareRuntime.Load)
variable (storeModel : AvxSquareRuntime.Store)
variable (xorModel : AvxSliceKernelRuntime.Xor)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_set1_epi64" => Avx512Register.broadcast
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.num.U64.to_ne_bytes" => X86PclmulRuntime.unsignedBytes
local notation "core.num.I64.from_ne_bytes" => X86PclmulRuntime.signedFromBytes
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "backend.x86_vpclmul512.store" => storeModel
local notation "backend.x86_vpclmul512.xor_assign" => xorModel
local notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.iter.ChunksMut" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks
local notation "core.slice.Slice.chunks_mut" => AvxHornerChunkRuntime.chunksMut
local notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice" =>
  (fun T => @AvxHornerChunkRuntime.nextShared T)
local notation "core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice" =>
  (fun T => @AvxHornerChunkRuntime.nextMutable T)
local notation "core.iter.traits.collect.IntoIterator.Blanket" => AvxSliceKernelRuntime.sharedBlanket
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" => AvxSliceKernelRuntime.zipConstruct
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  AvxSliceKernelRuntime.zipNext

/-- [bulksketch::backend::x86_vpclmul512::scale_kernel]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 329:4-334:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.scale_kernel_loop.body
  (CL : Bool) (scale : core.core_arch.x86.__m512i)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut
    Std.U64) (core.slice.iter.Chunks Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
    (core.slice.iter.Chunks Std.U64))) (core.iter.adapters.zip.Zip
    (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
      Std.U64)
      (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U64) iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (dst, src) := p
    let mi ← backend.x86_vpclmul512.load dst
    let mi1 ← backend.x86_vpclmul512.load src
    let mi2 ← backend.x86_vpclmul512.multiply CL mi1 scale
    let mi3 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi mi2
    let dst1 ← backend.x86_vpclmul512.store dst mi3
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (dst1, src))
               back z1))

local notation "backend.x86_vpclmul512.scale_kernel_loop.body" => (backend.x86_vpclmul512.scale_kernel_loop.body loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::scale_kernel]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 329:4-334:5 -/
@[rust_loop]
def backend.x86_vpclmul512.scale_kernel_loop
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64))
  (scale : core.core_arch.x86.__m512i) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
    (core.slice.iter.Chunks Std.U64))
  := do
  loop
    (fun (iter1, back1) => backend.x86_vpclmul512.scale_kernel_loop.body CL
      scale iter1 back1)
    (iter, back)

local notation "backend.x86_vpclmul512.scale_kernel_loop" => (backend.x86_vpclmul512.scale_kernel_loop loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::scale_kernel]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 321:0-335:1 -/
def backend.x86_vpclmul512.scale_kernel
  (CL : Bool) (dst : Slice Std.U64) (src : Slice Std.U64) (scale : Std.U64) :
  Result (Slice Std.U64)
  := do
  if scale = 0#u64
  then ok dst
  else
    if scale = 1#u64
    then backend.x86_vpclmul512.xor_assign dst src
    else
      let a ← core.num.U64.to_ne_bytes scale
      let i ← core.num.I64.from_ne_bytes a
      let scale1 ← core.core_arch.x86.avx512f._mm512_set1_epi64 i
      let (cm, chunks_mut_back) ← core.slice.Slice.chunks_mut dst 8#usize
      let c ← core.slice.Slice.chunks src 8#usize
      let (iter, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
          Std.U64) (core.iter.traits.collect.IntoIterator.Blanket
          (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
          Std.U64)) cm c
      let back ←
        backend.x86_vpclmul512.scale_kernel_loop CL iter (fun z => z) scale1
      let cm1 := trait_default_back back
      ok (chunks_mut_back cm1)

/-- [bulksketch::backend::x86_vpclmul512::square_kernel]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 358:4-361:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.square_kernel_loop.body
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut
    Std.U64) (core.slice.iter.Chunks Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
    (core.slice.iter.Chunks Std.U64))) (core.iter.adapters.zip.Zip
    (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
      Std.U64)
      (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U64) iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (dst, src) := p
    let value ← backend.x86_vpclmul512.load src
    let mi ← backend.x86_vpclmul512.multiply CL value value
    let dst1 ← backend.x86_vpclmul512.store dst mi
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (dst1, src))
               back z1))

local notation "backend.x86_vpclmul512.square_kernel_loop.body" => (backend.x86_vpclmul512.square_kernel_loop.body loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::square_kernel]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 358:4-361:5 -/
@[rust_loop]
def backend.x86_vpclmul512.square_kernel_loop
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
  (core.slice.iter.Chunks Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.ChunksMut Std.U64) (core.slice.iter.Chunks Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.ChunksMut Std.U64)
    (core.slice.iter.Chunks Std.U64))
  := do
  loop
    (fun (iter1, back1) => backend.x86_vpclmul512.square_kernel_loop.body CL
      iter1 back1)
    (iter, back)

local notation "backend.x86_vpclmul512.square_kernel_loop" => (backend.x86_vpclmul512.square_kernel_loop loadModel storeModel)

/-- [bulksketch::backend::x86_vpclmul512::square_kernel]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 357:0-362:1 -/
def backend.x86_vpclmul512.square_kernel
  (CL : Bool) (dst : Slice Std.U64) (src : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let (cm, chunks_mut_back) ← core.slice.Slice.chunks_mut dst 8#usize
  let c ← core.slice.Slice.chunks src 8#usize
  let (iter, trait_default_back) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.slice.iter.ChunksMut.Insts.CoreIterTraitsIteratorIteratorMutASlice
      Std.U64) (core.iter.traits.collect.IntoIterator.Blanket
      (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U64)) cm c
  let back ← backend.x86_vpclmul512.square_kernel_loop CL iter (fun z => z)
  let cm1 := trait_default_back back
  ok (chunks_mut_back cm1)

/-- [bulksketch::backend::x86_vpclmul512::update_single_block]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 755:0-759:1 -/
def backend.x86_vpclmul512.update_single_block
  (odd : Slice Std.U64) (offset : Std.Usize)
  (value : core.core_arch.x86.__m512i) :
  Result (Slice Std.U64)
  := do
  let i ← offset + 8#usize
  let i1 := Slice.len odd
  let «end» ← lift (core.cmp.impls.OrdUsize.min i i1)
  let (dst, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) odd
      { start := offset, «end» }
  let mi ← backend.x86_vpclmul512.load dst
  let mi1 ← core.core_arch.x86.avx512f._mm512_xor_si512 mi value
  let dst1 ← backend.x86_vpclmul512.store dst mi1
  ok (index_mut_back dst1)

end bulksketch
