-- Exact checked source projection. See extraction/affine-subspaces for provenance.
-- The shared triangular offset and both table loops are original stock declarations.
import Arithmetic.AffineLinearEvalGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

/-- [bulksketch::decode::affine::subspace_start]:
    Source: 'src/decode/affine.rs', lines 245:0-247:1 -/
def decode.affine.subspace_start (rank : Std.Usize) : Result Std.Usize := do
  let i ← rank + 1#usize
  let i1 ← rank * i
  i1 / 2#usize

/-- [bulksketch::decode::affine::subspaces]: loop body 1:
    Source: 'src/decode/affine.rs', lines 261:8-264:9 -/
@[rust_loop_body]
def decode.affine.subspaces_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (at_direction : Std.U64)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (output : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done output)
  | some p =>
    let (i, coefficient) := p
    let i1 ←
      backendcontractBulkKernelsInst.ArithmeticInst.mul at_direction
        coefficient
    let i2 ← Slice.index_usize output i
    let i3 ← lift (i2 ^^^ i1)
    let output1 ← Slice.update output i i3
    let i4 ← backendcontractBulkKernelsInst.ArithmeticInst.square coefficient
    let i5 ← i + 1#usize
    let i6 ← Slice.index_usize output1 i5
    let i7 ← lift (i6 ^^^ i4)
    let s ← Slice.update output1 i5 i7
    ok (cont (iter1, s))

/-- [bulksketch::decode::affine::subspaces]: loop 1:
    Source: 'src/decode/affine.rs', lines 261:8-264:9 -/
@[rust_loop]
def decode.affine.subspaces_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (output : Slice Std.U64) (at_direction : Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, output1) => decode.affine.subspaces_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst at_direction iter1
      output1)
    (iter, output)

/-- [bulksketch::decode::affine::subspaces]: loop body 0:
    Source: 'src/decode/affine.rs', lines 253:4-265:5 -/
@[rust_loop_body]
def decode.affine.subspaces_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (table : Slice Std.U64) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice Std.U64)) (Slice Std.U64))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done table)
  | some p =>
    let (rank, direction) := p
    let start ← decode.affine.subspace_start rank
    let i ← rank + 1#usize
    let next ← decode.affine.subspace_start i
    let ((previous, rest), split_at_mut_back) ←
      core.slice.Slice.split_at_mut table next
    let previous1 ←
      core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice
        Std.U64) previous { start, «end» := next }
    let i1 ← rank + 2#usize
    let (output, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
        { «end» := i1 }
    let at_direction ←
      decode.affine.linear_eval fieldBinaryFieldInst
        backendcontractBulkKernelsInst previous1 direction
    let output1 ← core.slice.Slice.fill core.clone.CloneU64 output 0#u64
    let i2 ← core.slice.Slice.iter previous1
    let iter2 ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64) i2
    let output2 ←
      decode.affine.subspaces_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst iter2 output1 at_direction
    let rest1 := index_mut_back output2
    let s := split_at_mut_back (previous, rest1)
    ok (cont (iter1, s))

/-- [bulksketch::decode::affine::subspaces]: loop 0:
    Source: 'src/decode/affine.rs', lines 253:4-265:5 -/
@[rust_loop]
def decode.affine.subspaces_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (table : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  loop
    (fun (iter1, table1) => decode.affine.subspaces_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 table1)
    (iter, table)

/-- [bulksketch::decode::affine::subspaces]:
    Source: 'src/decode/affine.rs', lines 251:0-266:1 -/
def decode.affine.subspaces
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (basis : Slice Std.U64) (table : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let s ← Slice.update table 0#usize 1#u64
  let i ← core.slice.Slice.iter basis
  let iter ←
    core.iter.traits.iterator.Iterator.enumerate.trait_default
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) i
  decode.affine.subspaces_loop0 fieldBinaryFieldInst
    backendcontractBulkKernelsInst iter s

end bulksketch
