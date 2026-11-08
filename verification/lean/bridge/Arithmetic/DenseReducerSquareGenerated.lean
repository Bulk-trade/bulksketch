-- Exact original Dense modular squaring and its six loop declarations.
import Arithmetic.DenseReducerSquareRuntime
import Arithmetic.DenseMulConvolutionGenerated

open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.unusedVariables false
set_option maxRecDepth 4096

namespace bulksketch

local notation "core.slice.Slice.last" => DenseReducerTableRuntime.last
local notation "core.option.Option.Insts.CoreCmpPartialEqOption.eq" => DenseReducerTableRuntime.optionEq
local notation "core.num.Usize.div_ceil" => DenseReducerSquareRuntime.divCeil

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]: loop body 1:
    Source: 'src/poly/dense.rs', lines 213:16-217:17 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (square : Std.U64)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
    ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)
    → core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      types.RawProduct) (core.iter.traits.iterator.IteratorSliceIter Std.U64)
      iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (slot, entry) := p
    let product ←
      backendcontractBulkKernelsInst.ArithmeticInst.raw_mul square entry
    let i ← lift (slot.lo ^^^ product.lo)
    let i1 ← lift (slot.hi ^^^ product.hi)
    ok (cont (iter1,
      fun z =>
        let z1 := next_back z (some ({ lo := i, hi := i1 }, entry))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]: loop 1:
    Source: 'src/poly/dense.rs', lines 213:16-217:17 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64))
  (square : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst square iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]: loop body 0:
    Source: 'src/poly/dense.rs', lines 207:8-219:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (table : Slice Std.U64) (degree : Std.Usize) (first_high : Std.Usize)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (accumulators : Slice types.RawProduct) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice types.RawProduct)) (Slice
    types.RawProduct))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done accumulators)
  | some p =>
    let (i, coefficient) := p
    let square ←
      backendcontractBulkKernelsInst.ArithmeticInst.square coefficient
    if i < first_high
    then
      let i1 ← 2#usize * i
      let rp ← Slice.index_usize accumulators i1
      let i2 ← lift (rp.lo ^^^ square)
      let (rp1, index_mut_back) ← Slice.index_mut_usize accumulators i1
      let s := index_mut_back { rp1 with lo := i2 }
      ok (cont (iter1, s))
    else
      let i1 ← i - first_high
      let start ← i1 * degree
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut accumulators
      let i2 ← start + degree
      let s ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) table
          { start, «end» := i2 }
      let (iter2, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          types.RawProduct)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          Std.U64) im s
      let (z, back) ←
        poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0_loop0
          fieldBinaryFieldInst backendcontractBulkKernelsInst iter2
          (fun z1 => z1) square
      let z1 := back z
      let im1 := trait_default_back z1
      let s1 := iter_mut_back im1
      ok (cont (iter1, s1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]: loop 0:
    Source: 'src/poly/dense.rs', lines 207:8-219:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (table : Slice Std.U64) (degree : Std.Usize)
  (accumulators : Slice types.RawProduct) (first_high : Std.Usize) :
  Result (Slice types.RawProduct)
  := do
  loop
    (fun (iter1, accumulators1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst table degree
      first_high iter1 accumulators1)
    (iter, accumulators)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]: loop body 2:
    Source: 'src/poly/dense.rs', lines 220:8-222:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter types.RawProduct))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter types.RawProduct) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter types.RawProduct)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    Std.U64) (core.slice.iter.Iter types.RawProduct)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter types.RawProduct) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter types.RawProduct)))
    ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter types.RawProduct)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter types.RawProduct)
    → core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter types.RawProduct))))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.iterator.IteratorSliceIter types.RawProduct)
      iter
  match o with
  | none => ok (done (iter1, fun z => let z1 := next_back z none
                                      back z1))
  | some p =>
    let (_, product) := p
    let target ← backendcontractBulkKernelsInst.ArithmeticInst.reduce product
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target, product))
               back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]: loop 2:
    Source: 'src/poly/dense.rs', lines 220:8-222:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter types.RawProduct))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
  (core.slice.iter.Iter types.RawProduct) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter types.RawProduct)) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter types.RawProduct)) × (core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut Std.U64) (core.slice.iter.Iter types.RawProduct)
    → core.iter.adapters.zip.Zip (core.slice.iter.IterMut Std.U64)
    (core.slice.iter.Iter types.RawProduct)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_mod_into]:
    Source: 'src/poly/dense.rs', lines 188:4-224:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Slice Std.U64) (modulus : Slice Std.U64) (table : Slice Std.U64)
  (dst : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result (Std.Usize × (Slice Std.U64) × (Slice types.RawProduct))
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
  let i2 := Slice.len a
  massert (i2 <= degree)
  let i3 := Slice.len dst
  massert (i3 >= degree)
  let i4 := Slice.len raw
  let i5 ← 2#usize * degree
  massert (i4 > i5)
  let left_val := Slice.len table
  let i6 ← degree / 2#usize
  let right_val ← degree * i6
  massert (left_val = right_val)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst
      { «end» := degree }
  let (b1, s1, raw1) ←
    backendcontractBulkKernelsInst.square_mod a table s raw
  if b1
  then
    let dst1 := index_mut_back s1
    let s2 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst1
        { «end» := degree }
    let i7 ← poly.dense.normalized_len s2
    ok (i7, dst1, raw1)
  else
    let (accumulators, index_mut_back1) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice types.RawProduct) raw1
        { «end» := degree }
    let rp ← types.RawProduct.Insts.CoreDefaultDefault.default
    let accumulators1 ←
      core.slice.Slice.fill types.RawProduct.Insts.CoreCloneClone accumulators
        rp
    let first_high ← core.num.Usize.div_ceil degree 2#usize
    let i7 ← core.slice.Slice.iter a
    let iter ←
      core.iter.traits.iterator.Iterator.enumerate.trait_default
        (core.iter.traits.iterator.IteratorSliceIter Std.U64) i7
    let dst1 := index_mut_back s1
    let accumulators2 ←
      poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop0
        fieldBinaryFieldInst backendcontractBulkKernelsInst iter table degree
        accumulators1 first_high
    let (s2, index_mut_back2) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst1
        { «end» := degree }
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut s2
    let i8 ← core.slice.Slice.iter accumulators2
    let (iter1, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        Std.U64) (core.iter.traits.collect.IntoIterator.Blanket
        (core.iter.traits.iterator.IteratorSliceIter types.RawProduct)) im i8
    let (z, back) ←
      poly.Dense.Insts.BulksketchPolyPolynomial.square_mod_into_loop1
        fieldBinaryFieldInst backendcontractBulkKernelsInst iter1
        (fun z1 => z1)
    let z1 := back z
    let im1 := trait_default_back z1
    let s3 := iter_mut_back im1
    let dst2 := index_mut_back2 s3
    let s4 ←
      core.slice.index.Slice.index
        (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst2
        { «end» := degree }
    let i9 ← poly.dense.normalized_len s4
    let raw2 := index_mut_back1 accumulators2
    ok (i9, dst2, raw2)

end bulksketch
