-- Exact original Dense square-table preparation and its loop.
import Arithmetic.DenseReducerTableRuntime

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false

namespace bulksketch

local notation "core.slice.Slice.last" => DenseReducerTableRuntime.last
local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => DenseReducerTableRuntime.optionEq

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::prepare_square_table]: loop body 0:
    Source: 'src/poly/dense.rs', lines 179:8-185:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (modulus : Slice Std.U64) (degree : Std.Usize) (rows : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (table : Slice Std.U64)
  (current : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U64) ×
    (Slice Std.U64)) ((Slice Std.U64) × (Slice Std.U64)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (table, current))
  | some row =>
    let i ← row * degree
    let i1 ← row + 1#usize
    let i2 ← i1 * degree
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) table
        { start := i, «end» := i2 }
    let s1 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s current
    if i1 != rows
    then
      let current1 ←
        poly.dense.times_x_mod fieldBinaryFieldInst
          backendcontractBulkKernelsInst current modulus
      let current2 ←
        poly.dense.times_x_mod fieldBinaryFieldInst
          backendcontractBulkKernelsInst current1 modulus
      let table1 := index_mut_back s1
      ok (cont (iter1, table1, current2))
    else let table1 := index_mut_back s1
         ok (cont (iter1, table1, current))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::prepare_square_table]: loop 0:
    Source: 'src/poly/dense.rs', lines 179:8-185:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.Usize) (modulus : Slice Std.U64)
  (table : Slice Std.U64) (degree : Std.Usize) (rows : Std.Usize)
  (current : Slice Std.U64) :
  Result ((Slice Std.U64) × (Slice Std.U64))
  := do
  loop
    (fun (iter1, table1, current1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table_loop.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst modulus degree rows
      iter1 table1 current1)
    (iter, table, current)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::prepare_square_table]:
    Source: 'src/poly/dense.rs', lines 167:4-186:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (modulus : Slice Std.U64) (table : Slice Std.U64) (work : Slice Std.U64) :
  Result ((Slice Std.U64) × (Slice Std.U64))
  := do
  let i := Slice.len modulus
  massert (i >= 4#usize)
  let o ← core.slice.Slice.last modulus
  let b ←
    core.option.Option.Insts.CoreCmpPartialEqOption.eq
      (core.cmp.PartialEqShared core.cmp.PartialEqU64) o (some 1#u64)
  massert b
  let i1 := Slice.len modulus
  let degree ← i1 - 1#usize
  let rows ← degree / 2#usize
  let i2 := Slice.len table
  let i3 ← degree * rows
  massert (i2 >= i3)
  let i4 := Slice.len work
  let i5 ← degree + 1#usize
  let i6 ← 4#usize * i5
  massert (i4 >= i6)
  let (current, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) work
      { «end» := degree }
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) modulus { «end» := degree }
  let current1 ←
    core.slice.Slice.copy_from_slice core.marker.CopyU64 current s
  let b1 ← core.num.Usize.is_multiple_of degree 2#usize
  let current2 ←
    if b1
    then ok current1
    else
      poly.dense.times_x_mod fieldBinaryFieldInst
        backendcontractBulkKernelsInst current1 modulus
  let (table1, current3) ←
    poly.Dense.Insts.BulksketchPolyPolynomial.prepare_square_table_loop
      fieldBinaryFieldInst backendcontractBulkKernelsInst
      { start := 0#usize, «end» := rows } modulus table degree rows current2
  let work1 := index_mut_back current3
  ok (table1, work1)

end bulksketch
