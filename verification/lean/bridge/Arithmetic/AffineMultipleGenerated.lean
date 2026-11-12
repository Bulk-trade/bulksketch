-- Exact original affine multiple source projection.
import Arithmetic.RootTraceGenerated
import Arithmetic.RebuiltLfsrRuntime
import Arithmetic.MutableZipRuntime

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxRecDepth 4096

variable (squareModel : RootTraceRuntime.ModularSquare)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into" => squareModel
local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

/-- [bulksketch::decode::affine::multiple]: loop body 1:
    Source: 'src/decode/affine.rs', lines 124:8-139:9 -/
@[rust_loop_body]
def decode.affine.multiple_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (d : Std.Usize) (width : Std.Usize) (rows : Slice Std.U64)
  (witnesses : Slice Std.U64) (column : Std.Usize)
  (iter : core.ops.range.Range Std.Usize) (vector : Slice Std.U64)
  (witness : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.Range Std.Usize) × (Slice Std.U64) ×
    (Slice Std.U64)) ((Slice Std.U64) × (Slice Std.U64) × (Option
    Std.Usize)))
  := do
  let (o, iter1) ←
    core.iter.range.IteratorRange.next core.iter.range.StepUsize iter
  match o with
  | none => ok (done (vector, witness, none))
  | some i =>
    let scale ← Slice.index_usize vector i
    if scale = 0#u64
    then ok (cont (iter1, vector, witness))
    else
      let i1 ← i * d
      let i2 ← i1 + i
      let i3 ← Slice.index_usize rows i2
      if i3 = 0#u64
      then ok (done (vector, witness, o))
      else
        let (s, index_mut_back) ←
          core.slice.index.Slice.index_mut
            (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) vector
            { start := i }
        let i4 ← i1 + i
        let i5 ← i + 1#usize
        let i6 ← i5 * d
        let s1 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) rows
            { start := i4, «end» := i6 }
        let s2 ←
          backendcontractBulkKernelsInst.ArithmeticInst.scale_xor s s1 scale
        let (s3, index_mut_back1) ←
          core.slice.index.Slice.index_mut
            (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
            Std.U64) witness { «end» := column }
        let i7 ← i * width
        let i8 ← i7 + column
        let i9 ← i8 + 1#usize
        let s4 ←
          core.slice.index.Slice.index
            (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) witnesses
            { start := i7, «end» := i9 }
        let s5 ←
          backendcontractBulkKernelsInst.ArithmeticInst.scale_xor s3 s4 scale
        let witness1 := index_mut_back1 s5
        let vector1 := index_mut_back s2
        ok (cont (iter1, vector1, witness1))

/-- [bulksketch::decode::affine::multiple]: loop 1:
    Source: 'src/decode/affine.rs', lines 124:8-139:9 -/
@[rust_loop]
def decode.affine.multiple_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.ops.range.Range Std.Usize) (d : Std.Usize) (width : Std.Usize)
  (rows : Slice Std.U64) (witnesses : Slice Std.U64) (vector : Slice Std.U64)
  (witness : Slice Std.U64) (column : Std.Usize) :
  Result ((Slice Std.U64) × (Slice Std.U64) × (Option Std.Usize))
  := do
  loop
    (fun (iter1, vector1, witness1) => decode.affine.multiple_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst d width rows
      witnesses column iter1 vector1 witness1)
    (iter, vector, witness)

/-- [bulksketch::decode::affine::multiple]: loop body 2:
    Source: 'src/decode/affine.rs', lines 149:8-154:9 -/
@[rust_loop_body]
def decode.affine.multiple_loop0_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (inverse : Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (_, value) := p
    let dst ← backendcontractBulkKernelsInst.ArithmeticInst.mul value inverse
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (dst, value))
               back z1))

/-- [bulksketch::decode::affine::multiple]: loop 2:
    Source: 'src/decode/affine.rs', lines 149:8-154:9 -/
@[rust_loop]
def decode.affine.multiple_loop0_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (inverse : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.affine.multiple_loop0_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst inverse iter1 back1)
    (iter, back)

/-- [bulksketch::decode::affine::multiple]: loop body 3:
    Source: 'src/decode/affine.rs', lines 155:8-160:9 -/
@[rust_loop_body]
def decode.affine.multiple_loop0_loop2.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (inverse : Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64))) ((core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (_, value) := p
    let dst ← backendcontractBulkKernelsInst.ArithmeticInst.mul value inverse
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (dst, value))
               back z1))

/-- [bulksketch::decode::affine::multiple]: loop 3:
    Source: 'src/decode/affine.rs', lines 155:8-160:9 -/
@[rust_loop]
def decode.affine.multiple_loop0_loop2
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64))
  (inverse : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter Std.U64) →
    core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) => decode.affine.multiple_loop0_loop2.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst inverse iter1 back1)
    (iter, back)

/-- [bulksketch::decode::affine::multiple]: loop body 0:
    Source: 'src/decode/affine.rs', lines 119:4-170:1 -/
@[rust_loop_body]
def decode.affine.multiple_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (index_mut_back : Slice Std.U64 → Slice Std.U64)
  (split_at_mut_back1 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (split_at_mut_back2 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (index_mut_back1 : Slice Std.U64 → Slice Std.U64)
  (polynomial : Slice Std.U64) (table : Slice Std.U64) (affine : Slice Std.U64)
  (d : Std.Usize) (width : Std.Usize)
  (iter : core.ops.range.RangeInclusive Std.Usize)
  (raw : Slice types.RawProduct) (rows : Slice Std.U64)
  (witnesses : Slice Std.U64) (residue : Slice Std.U64)
  (vector : Slice Std.U64) (witness : Slice Std.U64) :
  Result (ControlFlow ((core.ops.range.RangeInclusive Std.Usize) × (Slice
    types.RawProduct) × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64)
    × (Slice Std.U64) × (Slice Std.U64)) (Std.Usize × (Slice Std.U64) ×
    (Slice Std.U64) × (Slice Std.U64) × (Slice types.RawProduct)))
  := do
  let (o, iter1) ←
    core.ops.range.RangeInclusive.Insts.CoreIterTraitsIteratorIterator.next
      core.iter.range.StepUsize iter
  match o with
  | none => fail panic
  | some column =>
    let vector1 ←
      core.slice.Slice.copy_from_slice core.marker.CopyU64 vector residue
    let witness1 ← core.slice.Slice.fill core.clone.CloneU64 witness 0#u64
    let s ← Slice.update witness1 column 1#u64
    let (vector2, witness2, pivot) ←
      decode.affine.multiple_loop0_loop0 fieldBinaryFieldInst
        backendcontractBulkKernelsInst { start := 0#usize, «end» := d } d
        width rows witnesses vector1 s column
    match pivot with
    | none =>
      let (s1, index_mut_back2) ←
        core.slice.index.Slice.index_mut
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) affine { «end» := column }
      let s2 ←
        core.slice.index.Slice.index
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) witness2 { «end» := column }
      let s3 ← core.slice.Slice.copy_from_slice core.marker.CopyU64 s1 s2
      let i ← column + 1#usize
      let affine1 := index_mut_back2 s3
      let rest := index_mut_back witnesses
      let factors := split_at_mut_back (rows, rest)
      let rest1 := index_mut_back1 witness2
      let rest2 := split_at_mut_back2 (vector2, rest1)
      let work := split_at_mut_back1 (residue, rest2)
      ok (done (i, factors, affine1, work, raw))
    | some pivot1 =>
      let i ← Slice.index_usize vector2 pivot1
      let inverse ←
        if i = 1#u64
        then ok 1#u64
        else
          do
          let o1 ← backendcontractBulkKernelsInst.ArithmeticInst.inverse i
          core.option.Option.expect o1 (toStr "nonzero affine pivot")
      let i1 ← pivot1 * d
      let i2 ← i1 + pivot1
      let i3 ← pivot1 + 1#usize
      let i4 ← i3 * d
      let (s1, index_mut_back2) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) rows
          { start := i2, «end» := i4 }
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut s1
      let s2 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeFromUsizeSlice Std.U64) vector2
          { start := pivot1 }
      let (iter2, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im s2
      let (z, back) ←
        decode.affine.multiple_loop0_loop1 fieldBinaryFieldInst
          backendcontractBulkKernelsInst iter2 (fun z1 => z1) inverse
      let z1 := back z
      let i5 ← pivot1 * width
      let i6 ← i5 + column
      let i7 ← i6 + 1#usize
      let (s3, index_mut_back3) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) witnesses
          { start := i5, «end» := i7 }
      let (im1, iter_mut_back1) ← core.slice.Slice.iter_mut s3
      let s4 ←
        core.slice.index.Slice.index
          (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
          Std.U64) witness2 { «end» := column }
      let (iter3, trait_default_back1) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im1 s4
      let (z2, back1) ←
        decode.affine.multiple_loop0_loop2 fieldBinaryFieldInst
          backendcontractBulkKernelsInst iter3 (fun z3 => z3) inverse
      let z3 := back1 z2
      if column = 0#usize
      then
        let residue1 ←
          core.slice.Slice.fill core.clone.CloneU64 residue 0#u64
        let s5 ← Slice.update residue1 1#usize 1#u64
        let im2 := trait_default_back1 z3
        let s6 := iter_mut_back1 im2
        let s7 := index_mut_back3 s6
        let im3 := trait_default_back z1
        let s8 := iter_mut_back im3
        let s9 := index_mut_back2 s8
        ok (cont (iter1, raw, s9, s7, s5, vector2, witness2))
      else
        if column != d
        then
          let (_, vector3, raw1) ←
            poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
              fieldBinaryFieldInst backendcontractBulkKernelsInst residue
              polynomial table vector2 raw
          let residue1 ←
            core.slice.Slice.copy_from_slice core.marker.CopyU64 residue
              vector3
          let im2 := trait_default_back1 z3
          let s5 := iter_mut_back1 im2
          let s6 := index_mut_back3 s5
          let im3 := trait_default_back z1
          let s7 := iter_mut_back im3
          let s8 := index_mut_back2 s7
          ok (cont (iter1, raw1, s8, s6, residue1, vector3, witness2))
        else
          let im2 := trait_default_back1 z3
          let s5 := iter_mut_back1 im2
          let s6 := index_mut_back3 s5
          let im3 := trait_default_back z1
          let s7 := iter_mut_back im3
          let s8 := index_mut_back2 s7
          ok (cont (iter1, raw, s8, s6, residue, vector2, witness2))

local notation "decode.affine.multiple_loop0.body" => (decode.affine.multiple_loop0.body squareModel)

/-- [bulksketch::decode::affine::multiple]: loop 0:
    Source: 'src/decode/affine.rs', lines 119:4-170:1 -/
@[rust_loop]
def decode.affine.multiple_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (split_at_mut_back : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (index_mut_back : Slice Std.U64 → Slice Std.U64)
  (split_at_mut_back1 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (split_at_mut_back2 : ((Slice Std.U64) × (Slice Std.U64)) → Slice Std.U64)
  (index_mut_back1 : Slice Std.U64 → Slice Std.U64)
  (iter : core.ops.range.RangeInclusive Std.Usize) (polynomial : Slice Std.U64)
  (table : Slice Std.U64) (affine : Slice Std.U64)
  (raw : Slice types.RawProduct) (d : Std.Usize) (width : Std.Usize)
  (rows : Slice Std.U64) (witnesses : Slice Std.U64) (residue : Slice Std.U64)
  (vector : Slice Std.U64) (witness : Slice Std.U64) :
  Result (Std.Usize × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice types.RawProduct))
  := do
  loop
    (fun (iter1, raw1, rows1, witnesses1, residue1, vector1, witness1) =>
      decode.affine.multiple_loop0.body fieldBinaryFieldInst
      backendcontractBulkKernelsInst split_at_mut_back index_mut_back
      split_at_mut_back1 split_at_mut_back2 index_mut_back1 polynomial table
      affine d width iter1 raw1 rows1 witnesses1 residue1 vector1 witness1)
    (iter, raw, rows, witnesses, residue, vector, witness)

local notation "decode.affine.multiple_loop0" => (decode.affine.multiple_loop0 squareModel)

/-- [bulksketch::decode::affine::multiple]:
    Source: 'src/decode/affine.rs', lines 100:0-170:1 -/
def decode.affine.multiple
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (polynomial : Slice Std.U64) (table : Slice Std.U64)
  (factors : Slice Std.U64) (affine : Slice Std.U64) (work : Slice Std.U64)
  (raw : Slice types.RawProduct) :
  Result (Std.Usize × (Slice Std.U64) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice types.RawProduct))
  := do
  let i := Slice.len polynomial
  let d ← i - 1#usize
  let width ← d + 1#usize
  let i1 ← d * d
  let ((rows, rest), split_at_mut_back) ←
    core.slice.Slice.split_at_mut factors i1
  let i2 ← d * width
  let (witnesses, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest
      { «end» := i2 }
  let rows1 ← core.slice.Slice.fill core.clone.CloneU64 rows 0#u64
  let witnesses1 ← core.slice.Slice.fill core.clone.CloneU64 witnesses 0#u64
  let ((residue, rest1), split_at_mut_back1) ←
    core.slice.Slice.split_at_mut work d
  let ((vector, rest2), split_at_mut_back2) ←
    core.slice.Slice.split_at_mut rest1 d
  let (witness, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rest2
      { «end» := width }
  let residue1 ← core.slice.Slice.fill core.clone.CloneU64 residue 0#u64
  let s ← Slice.update residue1 0#usize 1#u64
  let iter ← core.ops.range.RangeInclusive.new 0#usize d
  decode.affine.multiple_loop0 fieldBinaryFieldInst
    backendcontractBulkKernelsInst split_at_mut_back index_mut_back
    split_at_mut_back1 split_at_mut_back2 index_mut_back1 iter polynomial table
    affine raw d width rows1 witnesses1 s vector witness
end bulksketch
