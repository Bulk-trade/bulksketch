-- Original checked AVX free and public insertion dispatch declarations.
import Arithmetic.AvxHornerChunkRuntime
import Arithmetic.PortableInsertionGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Aeneas.Std.AvxInsertDispatchRuntime

abbrev Single := Slice U64 → U64 → Result (Slice U64)
abbrev SingleCapacity := Usize → Slice U64 → U64 → Result (Slice U64)
abbrev Batch := Slice U64 → Slice U64 → Result (Slice U64)
abbrev Tile := Usize → Bool → Batch

end Aeneas.Std.AvxInsertDispatchRuntime

namespace bulksketch

variable (insert18Model : AvxInsertDispatchRuntime.Single)
variable (insert32Model : AvxInsertDispatchRuntime.Single)
variable (singleModel : AvxInsertDispatchRuntime.SingleCapacity)
variable (sparseModel : AvxInsertDispatchRuntime.Batch)
variable (tileModel : AvxInsertDispatchRuntime.Tile)

local notation "core.slice.iter.Chunks" => AvxHornerChunkRuntime.ChunkState
local notation "core.slice.Slice.chunks" => AvxHornerChunkRuntime.chunks
local notation "core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next" =>
  AvxHornerChunkRuntime.nextShared
local notation "backend.x86_vpclmul512.insert_18" => insert18Model
local notation "backend.x86_vpclmul512.insert_32" => insert32Model
local notation "backend.x86_vpclmul512.insert_single" => singleModel
local notation "backend.x86_vpclmul512.insert_sparse" => sparseModel
local notation "backend.x86_vpclmul512.insert_tile" => tileModel

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop body 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_loop0.body
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done odd)
  | some ids =>
    let i := Slice.len ids
    match i.val with
    | 0 => ok (cont (iter1, odd))
    | _ =>
      if 1#usize <= i
      then
        if i <= 8#usize
        then
          let odd1 ← backend.x86_vpclmul512.insert_tile 1#usize true odd ids
          ok (cont (iter1, odd1))
        else
          if 9#usize <= i
          then
            if i <= 16#usize
            then
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 2#usize true odd ids
              ok (cont (iter1, odd1))
            else
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 4#usize false odd ids
              ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
      else
        if 9#usize <= i
        then
          if i <= 16#usize
          then
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 2#usize true odd ids
            ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
        else
          let odd1 ← backend.x86_vpclmul512.insert_tile 4#usize false odd ids
          ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.insert_loop0.body" => (backend.x86_vpclmul512.insert_loop0.body tileModel)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop 0:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_loop0
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) => backend.x86_vpclmul512.insert_loop0.body iter1 odd1)
    (iter, odd)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop body 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_loop1.body
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done odd)
  | some ids =>
    let i := Slice.len ids
    match i.val with
    | 0 => ok (cont (iter1, odd))
    | _ =>
      if 1#usize <= i
      then
        if i <= 8#usize
        then
          let odd1 ← backend.x86_vpclmul512.insert_tile 1#usize true odd ids
          ok (cont (iter1, odd1))
        else
          if 9#usize <= i
          then
            if i <= 16#usize
            then
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 2#usize true odd ids
              ok (cont (iter1, odd1))
            else
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 4#usize false odd ids
              ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
      else
        if 9#usize <= i
        then
          if i <= 16#usize
          then
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 2#usize true odd ids
            ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
        else
          let odd1 ← backend.x86_vpclmul512.insert_tile 4#usize false odd ids
          ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.insert_loop1.body" => (backend.x86_vpclmul512.insert_loop1.body tileModel)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop 1:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_loop1
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) => backend.x86_vpclmul512.insert_loop1.body iter1 odd1)
    (iter, odd)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop body 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_loop2.body
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done odd)
  | some ids =>
    let i := Slice.len ids
    match i.val with
    | 0 => ok (cont (iter1, odd))
    | _ =>
      if 1#usize <= i
      then
        if i <= 8#usize
        then
          let odd1 ← backend.x86_vpclmul512.insert_tile 1#usize true odd ids
          ok (cont (iter1, odd1))
        else
          if 9#usize <= i
          then
            if i <= 16#usize
            then
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 2#usize true odd ids
              ok (cont (iter1, odd1))
            else
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 4#usize false odd ids
              ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
      else
        if 9#usize <= i
        then
          if i <= 16#usize
          then
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 2#usize true odd ids
            ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
        else
          let odd1 ← backend.x86_vpclmul512.insert_tile 4#usize false odd ids
          ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.insert_loop2.body" => (backend.x86_vpclmul512.insert_loop2.body tileModel)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop 2:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_loop2
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) => backend.x86_vpclmul512.insert_loop2.body iter1 odd1)
    (iter, odd)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop body 3:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop_body]
def backend.x86_vpclmul512.insert_loop3.body
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (ControlFlow ((core.slice.iter.Chunks Std.U64) × (Slice Std.U64))
    (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.slice.iter.Chunks.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next
      iter
  match o with
  | none => ok (done odd)
  | some ids =>
    let i := Slice.len ids
    match i.val with
    | 0 => ok (cont (iter1, odd))
    | _ =>
      if 1#usize <= i
      then
        if i <= 8#usize
        then
          let odd1 ← backend.x86_vpclmul512.insert_tile 1#usize true odd ids
          ok (cont (iter1, odd1))
        else
          if 9#usize <= i
          then
            if i <= 16#usize
            then
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 2#usize true odd ids
              ok (cont (iter1, odd1))
            else
              let odd1 ←
                backend.x86_vpclmul512.insert_tile 4#usize false odd ids
              ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
      else
        if 9#usize <= i
        then
          if i <= 16#usize
          then
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 2#usize true odd ids
            ok (cont (iter1, odd1))
          else
            let odd1 ←
              backend.x86_vpclmul512.insert_tile 4#usize false odd ids
            ok (cont (iter1, odd1))
        else
          let odd1 ← backend.x86_vpclmul512.insert_tile 4#usize false odd ids
          ok (cont (iter1, odd1))

local notation "backend.x86_vpclmul512.insert_loop3.body" => (backend.x86_vpclmul512.insert_loop3.body tileModel)

/-- [bulksketch::backend::x86_vpclmul512::insert]: loop 3:
    Source: 'src/backend/x86_vpclmul512.rs', lines 417:4-424:5 -/
@[rust_loop]
def backend.x86_vpclmul512.insert_loop3
  (iter : core.slice.iter.Chunks Std.U64) (odd : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, odd1) => backend.x86_vpclmul512.insert_loop3.body iter1 odd1)
    (iter, odd)

local notation "backend.x86_vpclmul512.insert_loop0" => (backend.x86_vpclmul512.insert_loop0 tileModel)
local notation "backend.x86_vpclmul512.insert_loop1" => (backend.x86_vpclmul512.insert_loop1 tileModel)
local notation "backend.x86_vpclmul512.insert_loop2" => (backend.x86_vpclmul512.insert_loop2 tileModel)
local notation "backend.x86_vpclmul512.insert_loop3" => (backend.x86_vpclmul512.insert_loop3 tileModel)

/-- [bulksketch::backend::x86_vpclmul512::insert]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 396:0-425:1 -/
def backend.x86_vpclmul512.insert
  (odd : Slice Std.U64) (ids : Slice Std.U64) : Result (Slice Std.U64) := do
  let b ← core.slice.Slice.is_empty odd
  if b
  then ok odd
  else
    let b1 ← core.slice.Slice.is_empty ids
    if b1
    then ok odd
    else
      let i := Slice.len ids
      if i = 1#usize
      then
        let i1 := Slice.len odd
        match i1.val with
        | 18 =>
          let i2 ← Slice.index_usize ids 0#usize
          backend.x86_vpclmul512.insert_18 odd i2
        | 32 =>
          let i2 ← Slice.index_usize ids 0#usize
          backend.x86_vpclmul512.insert_32 odd i2
        | 72 =>
          let i2 ← Slice.index_usize ids 0#usize
          backend.x86_vpclmul512.insert_single 72#usize odd i2
        | 89 =>
          let i2 ← Slice.index_usize ids 0#usize
          backend.x86_vpclmul512.insert_single 89#usize odd i2
        | _ =>
          let i2 := Slice.len ids
          if i2 <= 4#usize
          then
            let i3 := Slice.len odd
            match i3.val with
            | 18 => backend.x86_vpclmul512.insert_sparse odd ids
            | 72 => backend.x86_vpclmul512.insert_sparse odd ids
            | 89 => backend.x86_vpclmul512.insert_sparse odd ids
            | _ =>
              let iter ← core.slice.Slice.chunks ids 32#usize
              backend.x86_vpclmul512.insert_loop0 iter odd
          else
            let iter ← core.slice.Slice.chunks ids 32#usize
            backend.x86_vpclmul512.insert_loop1 iter odd
      else
        let i1 := Slice.len ids
        if i1 <= 4#usize
        then
          let i2 := Slice.len odd
          match i2.val with
          | 18 => backend.x86_vpclmul512.insert_sparse odd ids
          | 72 => backend.x86_vpclmul512.insert_sparse odd ids
          | 89 => backend.x86_vpclmul512.insert_sparse odd ids
          | _ =>
            let iter ← core.slice.Slice.chunks ids 32#usize
            backend.x86_vpclmul512.insert_loop2 iter odd
        else
          let iter ← core.slice.Slice.chunks ids 32#usize
          backend.x86_vpclmul512.insert_loop3 iter odd

local notation "backend.x86_vpclmul512.insert" =>
  (backend.x86_vpclmul512.insert insert18Model insert32Model singleModel sparseModel tileModel)

/-- [bulksketch::backend::x86_vpclmul512::{impl bulksketch::backend::contract::BulkKernels<F> for bulksketch::backend::x86_vpclmul512::Vpclmul512}::insert_nonzero]:
    Source: 'src/backend/x86_vpclmul512.rs', lines 133:4-142:5 -/
def
  backend.x86_vpclmul512.Vpclmul512.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
  {F : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (odd : Slice Std.U64) (ids : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let b ← core.slice.Slice.is_empty odd
  if b
  then ok odd
  else
    let b1 ← core.slice.Slice.is_empty ids
    if b1
    then ok odd
    else
      let i ← fieldBinaryFieldInst.BITS
      if i != 64#u32
      then
        backend.portable.Portable.Insts.BulksketchBackendContractBulkKernels.insert_nonzero
          fieldBinaryFieldInst odd ids
      else backend.x86_vpclmul512.insert odd ids

end bulksketch
