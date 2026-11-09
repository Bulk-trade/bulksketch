-- Verbatim declarations from the checked original tile capture.
import Arithmetic.AvxTileRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace bulksketch

variable (loadModel : AvxSquareRuntime.Load)

local notation "core.core_arch.x86.__m512i" => Avx512Register.Word512
local notation "core.core_arch.x86.avx512f._mm512_xor_si512" => Avx512Register.xorWords
local notation "core.core_arch.x86.avx512f._mm512_setzero_si512" => AvxSquareRuntime.zero
local notation "core.core_arch.x86.__m512i.Insts.CoreMarkerCopy" => AvxTileRuntime.vectorCopy
local notation "backend.x86_vpclmul512.load" => loadModel
local notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks
local notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice" =>
  AvxTileRuntime.chunkWords
local notation "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT" =>
  AvxTileRuntime.mutableWords
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair" =>
  AvxTileRuntime.bothMutableWords
local notation "core.iter.traits.collect.IntoIterator.Blanket" =>
  (fun (it : AvxTileRuntime.ChunkWords) => it)
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" =>
  AvxTileRuntime.zipConstruct
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" =>
  AvxTileRuntime.zipNext
local notation "MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut" =>
  AvxTileRuntime.mutableArrayWords
local notation "MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter" =>
  core.slice.Slice.iter_mut
local notation "core.iter.traits.iterator.Iterator.copied.default" => AvxTileRuntime.copied
local notation "core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.fold" =>
  AvxTileRuntime.foldCopied

/-- [bulksketch::backend::x86_vpclmul512::insert_tile::{closure}]
    Source: 'src/backend/x86_vpclmul512.rs', lines 449:42-449:75 -/
@[reducible]
def backend.x86_vpclmul512.insert_tile.closure (W : Std.Usize) (CL : Bool) :=
Unit

/-- [bulksketch::backend::x86_vpclmul512::insert_tile::{impl core::ops::function::FnMut<(core::core_arch::x86::__m512i, core::core_arch::x86::__m512i), core::core_arch::x86::__m512i> for bulksketch::backend::x86_vpclmul512::insert_tile::{closure}<W, CL>}::call_mut]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 449:42-449:75 -/
def
  backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i.call_mut
  {W : Std.Usize} {CL : Bool}
  (c : backend.x86_vpclmul512.insert_tile.closure W CL)
  (tupled_args : (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)) :
  Result (core.core_arch.x86.__m512i ×
    (backend.x86_vpclmul512.insert_tile.closure W CL))
  := do
  let (sum, p) := tupled_args
  let mi ← core.core_arch.x86.avx512f._mm512_xor_si512 sum p
  ok (mi, c)

/-- [bulksketch::backend::x86_vpclmul512::insert_tile::{impl core::ops::function::FnOnce<(core::core_arch::x86::__m512i, core::core_arch::x86::__m512i), core::core_arch::x86::__m512i> for bulksketch::backend::x86_vpclmul512::insert_tile::{closure}<W, CL>}::call_once]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 449:42-449:75 -/
def
  backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnOncePair__m512i__m512i__m512i.call_once
  {W : Std.Usize} {CL : Bool}
  (c : backend.x86_vpclmul512.insert_tile.closure W CL)
  (p : (core.core_arch.x86.__m512i × core.core_arch.x86.__m512i)) :
  Result core.core_arch.x86.__m512i
  := do
  let (mi, _) ←
    backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i.call_mut
      c p
  ok mi

/-- Trait implementation: [bulksketch::backend::x86_vpclmul512::insert_tile::{impl core::ops::function::FnOnce<(core::core_arch::x86::__m512i, core::core_arch::x86::__m512i), core::core_arch::x86::__m512i> for bulksketch::backend::x86_vpclmul512::insert_tile::{closure}<W, CL>}]
    Source: 'src/backend/x86_vpclmul512.rs', lines 449:42-449:75 -/
@[reducible]
def
  backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnOncePair__m512i__m512i__m512i
  (W : Std.Usize) (CL : Bool) : core.ops.function.FnOnce
  (backend.x86_vpclmul512.insert_tile.closure W CL) (core.core_arch.x86.__m512i
  × core.core_arch.x86.__m512i) core.core_arch.x86.__m512i := {
  call_once :=
    backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnOncePair__m512i__m512i__m512i.call_once
}

/-- Trait implementation: [bulksketch::backend::x86_vpclmul512::insert_tile::{impl core::ops::function::FnMut<(core::core_arch::x86::__m512i, core::core_arch::x86::__m512i), core::core_arch::x86::__m512i> for bulksketch::backend::x86_vpclmul512::insert_tile::{closure}<W, CL>}]
    Source: 'src/backend/x86_vpclmul512.rs', lines 449:42-449:75 -/
@[reducible]
def
  backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i
  (W : Std.Usize) (CL : Bool) : core.ops.function.FnMut
  (backend.x86_vpclmul512.insert_tile.closure W CL) (core.core_arch.x86.__m512i
  × core.core_arch.x86.__m512i) core.core_arch.x86.__m512i := {
  FnOnceInst :=
    backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnOncePair__m512i__m512i__m512i
    W CL
  call_mut :=
    backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i.call_mut
}

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 441:4-444:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_tile_loop0.body
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64))
  (back : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64) →
  core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64))
  (back1 : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64) →
  core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i)
    (core.slice.iter.IterMut core.core_arch.x86.__m512i))
    (core.slice.iter.Chunks Std.U64)) × (core.iter.adapters.zip.Zip
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    core.core_arch.x86.__m512i) (core.slice.iter.IterMut
    core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64) →
    core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i)
    (core.slice.iter.IterMut core.core_arch.x86.__m512i))
    (core.slice.iter.Chunks Std.U64)) × (core.iter.adapters.zip.Zip
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    core.core_arch.x86.__m512i) (core.slice.iter.IterMut
    core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64) →
    core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i)
    (core.slice.iter.IterMut core.core_arch.x86.__m512i))
    (core.slice.iter.Chunks Std.U64))) ((core.iter.adapters.zip.Zip
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    core.core_arch.x86.__m512i) (core.slice.iter.IterMut
    core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i)
    (core.slice.iter.IterMut core.core_arch.x86.__m512i))
    (core.slice.iter.Chunks Std.U64))))
  := do
  let (o, iter1, next_back, next_back1) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      core.core_arch.x86.__m512i)
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      core.core_arch.x86.__m512i))
      (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U64) iter
  match o with
  | none =>
    ok (done (let z := next_back1 iter1 none
              back z, let z := next_back iter1 none
                      back1 z))
  | some p =>
    let ((power, step), ids) := p
    let power1 ← backend.x86_vpclmul512.load ids
    let step1 ← backend.x86_vpclmul512.multiply CL power1 power1
    ok (cont (iter1,
      fun z => let z1 := next_back1 z (some ((power, step1), ids))
               back z1,
      fun z => let z1 := next_back z (some ((power1, step), ids))
               back1 z1))

local notation "backend.x86_vpclmul512.insert_tile_loop0.body" => (backend.x86_vpclmul512.insert_tile_loop0.body loadModel)

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 441:4-444:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_tile_loop0
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64))
  (back : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64) →
  core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64))
  (back1 : core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64) →
  core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.IterMut
  core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64)) :
  Result ((core.iter.adapters.zip.Zip (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i)
    (core.slice.iter.IterMut core.core_arch.x86.__m512i))
    (core.slice.iter.Chunks Std.U64)) × (core.iter.adapters.zip.Zip
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    core.core_arch.x86.__m512i) (core.slice.iter.IterMut
    core.core_arch.x86.__m512i)) (core.slice.iter.Chunks Std.U64)))
  := do
  loop
    (fun (iter1, back2, back3) => backend.x86_vpclmul512.insert_tile_loop0.body
      CL iter1 back2 back3)
    (iter, back, back1)

local notation "backend.x86_vpclmul512.insert_tile_loop0" => (backend.x86_vpclmul512.insert_tile_loop0 loadModel)

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]: loop body 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 453:8-456:9 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_tile_loop1_loop0.body
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut
  core.core_arch.x86.__m512i) (core.slice.iter.Iter
  core.core_arch.x86.__m512i))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut
  core.core_arch.x86.__m512i) (core.slice.iter.Iter core.core_arch.x86.__m512i)
  → core.iter.adapters.zip.Zip (core.slice.iter.IterMut
  core.core_arch.x86.__m512i) (core.slice.iter.Iter
  core.core_arch.x86.__m512i)) (sum : core.core_arch.x86.__m512i) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i)) × core.core_arch.x86.__m512i)
    (core.core_arch.x86.__m512i × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      core.core_arch.x86.__m512i) (core.iter.traits.iterator.IteratorSliceIter
      core.core_arch.x86.__m512i) iter
  match o with
  | none => ok (done (sum, iter1, fun z => let z1 := next_back z none
                                           back z1))
  | some p =>
    let (power, step) := p
    let power1 ← backend.x86_vpclmul512.multiply CL power step
    let sum1 ← core.core_arch.x86.avx512f._mm512_xor_si512 sum power1
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (power1, step))
               back z1, sum1))

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]: loop 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 453:8-456:9 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_tile_loop1_loop0
  (CL : Bool)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut
  core.core_arch.x86.__m512i) (core.slice.iter.Iter
  core.core_arch.x86.__m512i))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut
  core.core_arch.x86.__m512i) (core.slice.iter.Iter core.core_arch.x86.__m512i)
  → core.iter.adapters.zip.Zip (core.slice.iter.IterMut
  core.core_arch.x86.__m512i) (core.slice.iter.Iter
  core.core_arch.x86.__m512i)) (sum : core.core_arch.x86.__m512i) :
  Result (core.core_arch.x86.__m512i × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut core.core_arch.x86.__m512i) (core.slice.iter.Iter
    core.core_arch.x86.__m512i)))
  := do
  loop
    (fun (iter1, back1, sum1) =>
      backend.x86_vpclmul512.insert_tile_loop1_loop0.body CL iter1 back1 sum1)
    (iter, back, sum)

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]: loop body 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 451:4-458:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_tile_loop1.body
  {W : Std.Usize} (CL : Bool) (mi : core.core_arch.x86.__m512i)
  (steps : Array core.core_arch.x86.__m512i W)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (powers : Array core.core_arch.x86.__m512i W) :
  Result (ControlFlow ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64) ×
    (Array core.core_arch.x86.__m512i W)) ((core.slice.iter.IterMut Std.U64) ×
    (core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)))
  := do
  let (o, iter1, next_back) ← core.slice.iter.IteratorIterMut.next iter
  match o with
  | none => ok (done (iter1, fun im => let im1 := next_back im none
                                       back im1))
  | some syndrome =>
    let (s, to_slice_mut_back) ← lift (Array.to_slice_mut powers)
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
    let (iter2, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        core.core_arch.x86.__m512i)
        (SharedArray.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
        core.core_arch.x86.__m512i W) im steps
    let (sum, z, back1) ←
      backend.x86_vpclmul512.insert_tile_loop1_loop0 CL iter2 (fun z1 => z1) mi
    let i ← backend.x86_vpclmul512.horizontal_xor sum
    let syndrome1 ← lift (syndrome ^^^ i)
    let z1 := back1 z
    let im1 := trait_default_back z1
    let s1 := iter_mut_back im1
    let a := to_slice_mut_back s1
    ok (cont (iter1,
      fun im2 => let im3 := next_back im2 (some syndrome1)
                 back im3, a))

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]: loop 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 451:4-458:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_tile_loop1
  {W : Std.Usize} (CL : Bool) (mi : core.core_arch.x86.__m512i)
  (iter : core.slice.iter.IterMut Std.U64)
  (back : core.slice.iter.IterMut Std.U64 → core.slice.iter.IterMut Std.U64)
  (powers : Array core.core_arch.x86.__m512i W)
  (steps : Array core.core_arch.x86.__m512i W) :
  Result ((core.slice.iter.IterMut Std.U64) × (core.slice.iter.IterMut Std.U64
    → core.slice.iter.IterMut Std.U64))
  := do
  loop
    (fun (iter1, back1, powers1) =>
      backend.x86_vpclmul512.insert_tile_loop1.body CL mi steps iter1 back1
      powers1)
    (iter, back, powers)

/-- [bulksketch::backend::x86_vpclmul512::insert_tile]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 438:0-459:1 -/
def backend.x86_vpclmul512.insert_tile
  (W : Std.Usize) (CL : Bool) (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let mi ← core.core_arch.x86.avx512f._mm512_setzero_si512
  let powers := Array.repeat W mi
  let (s, to_slice_mut_back) ← lift (Array.to_slice_mut powers)
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
  let (z, trait_default_back, trait_default_back1) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      core.core_arch.x86.__m512i)
      (MutAArray.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut
      core.core_arch.x86.__m512i W) im powers
  let c ← core.slice.Slice.chunks ids 8#usize
  let (iter, trait_default_back2, trait_default_back3) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      core.core_arch.x86.__m512i)
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      core.core_arch.x86.__m512i))
      (core.iter.traits.collect.IntoIterator.Blanket
      (core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice
      Std.U64)) z c
  let (back, back1) ←
    backend.x86_vpclmul512.insert_tile_loop0 CL iter (fun z1 => z1)
      (fun z1 => z1)
  let z1 := trait_default_back2 back1
  let im1 := trait_default_back z1
  let s1 := iter_mut_back im1
  let powers1 := to_slice_mut_back s1
  let s2 ← lift (Array.to_slice powers1)
  let i ← core.slice.Slice.iter s2
  let c1 ←
    core.iter.traits.iterator.Iterator.copied.default
      (core.iter.traits.iterator.IteratorSliceIter core.core_arch.x86.__m512i)
      core.core_arch.x86.__m512i.Insts.CoreMarkerCopy
      (core.iter.traits.iterator.IteratorSliceIter core.core_arch.x86.__m512i)
      i
  let mi1 ←
    core.iter.adapters.copied.Copied.Insts.CoreIterTraitsIteratorIterator.fold
      (core.iter.traits.iterator.IteratorSliceIter core.core_arch.x86.__m512i)
      core.core_arch.x86.__m512i.Insts.CoreMarkerCopy
      (backend.x86_vpclmul512.insert_tile.closure.Insts.CoreOpsFunctionFnMutPair__m512i__m512i__m512i
      W CL) c1 mi ()
  let i1 ← backend.x86_vpclmul512.horizontal_xor mi1
  let i2 ← Slice.index_usize odd 0#usize
  let i3 ← lift (i2 ^^^ i1)
  let odd1 ← Slice.update odd 0#usize i3
  let (s3, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) odd1
      { start := 1#usize }
  let (iter1, into_iter_back) ←
    MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter s3
  let z2 := trait_default_back3 back
  let steps := trait_default_back1 z2
  let (im2, back2) ←
    backend.x86_vpclmul512.insert_tile_loop1 CL mi iter1 (fun im3 => im3)
      powers1 steps
  let im3 := back2 im2
  let s4 := into_iter_back im3
  ok (index_mut_back s4)

end bulksketch
