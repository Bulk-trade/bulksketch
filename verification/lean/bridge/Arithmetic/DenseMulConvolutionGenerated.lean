-- Exact original Dense convolution declarations. Imports are adapted only.
module
public import Arithmetic.DenseMulReductionGenerated
public import Arithmetic.DenseNormalizationGenerated
public import Arithmetic.OddRecurrenceGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::types::{impl core::clone::Clone for bulksketch::types::RawProduct}::clone]:
    Source: 'src/types.rs', lines 266:9-266:14
    Visibility: public -/
def types.RawProduct.Insts.CoreCloneClone.clone
  (self : types.RawProduct) : Result types.RawProduct := do
  ok self

/-- Trait implementation: [bulksketch::types::{impl core::clone::Clone for bulksketch::types::RawProduct}]
    Source: 'src/types.rs', lines 266:9-266:14 -/
@[reducible]
def types.RawProduct.Insts.CoreCloneClone : core.clone.Clone types.RawProduct
  := {
  clone := types.RawProduct.Insts.CoreCloneClone.clone
}

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]: loop body 1:
    Source: 'src/poly/dense.rs', lines 18:12-22:13 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (left : Std.U64)
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
    let (slot, right) := p
    let product ←
      backendcontractBulkKernelsInst.ArithmeticInst.raw_mul left right
    let i ← lift (slot.lo ^^^ product.lo)
    let i1 ← lift (slot.hi ^^^ product.hi)
    ok (cont (iter1,
      fun z =>
        let z1 := next_back z (some ({ lo := i, hi := i1 }, right))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]: loop 1:
    Source: 'src/poly/dense.rs', lines 18:12-22:13 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64))
  (left : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst left iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]: loop body 0:
    Source: 'src/poly/dense.rs', lines 17:8-23:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (b : Slice Std.U64)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (raw : Slice types.RawProduct) :
  Result (ControlFlow ((core.iter.adapters.enumerate.Enumerate
    (core.slice.iter.Iter Std.U64)) × (Slice types.RawProduct)) (Slice
    types.RawProduct))
  := do
  let (o, iter1) ←
    core.iter.adapters.enumerate.IteratorEnumerate.next
      (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done raw)
  | some p =>
    let (i, left) := p
    let i1 := Slice.len b
    let i2 ← i + i1
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.slice.index.SliceIndexRangeUsizeSlice types.RawProduct) raw
        { start := i, «end» := i2 }
    let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
    let (iter2, trait_default_back) ←
      core.iter.traits.iterator.Iterator.zip.trait_default
        (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
        types.RawProduct)
        (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter Std.U64)
        im b
    let (z, back) ←
      poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0_loop0
        fieldBinaryFieldInst backendcontractBulkKernelsInst iter2
        (fun z1 => z1) left
    let z1 := back z
    let im1 := trait_default_back z1
    let s1 := iter_mut_back im1
    let s2 := index_mut_back s1
    ok (cont (iter1, s2))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]: loop 0:
    Source: 'src/poly/dense.rs', lines 17:8-23:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.enumerate.Enumerate (core.slice.iter.Iter
  Std.U64)) (b : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result (Slice types.RawProduct)
  := do
  loop
    (fun (iter1, raw1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst b iter1 raw1)
    (iter, raw)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]:
    Source: 'src/poly/dense.rs', lines 7:4-28:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Slice Std.U64) (b : Slice Std.U64) (dst : Slice Std.U64)
  (raw : Slice types.RawProduct) :
  Result (Std.Usize × (Slice Std.U64) × (Slice types.RawProduct))
  := do
  let b1 ← core.slice.Slice.is_empty a
  if b1
  then ok (0#usize, dst, raw)
  else
    let b2 ← core.slice.Slice.is_empty b
    if b2
    then ok (0#usize, dst, raw)
    else
      let i := Slice.len a
      let i1 := Slice.len b
      let size ← i + i1
      let i2 := Slice.len dst
      massert (i2 >= size)
      let i3 := Slice.len raw
      massert (i3 >= size)
      let len ← size - 1#usize
      let (s, index_mut_back) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice types.RawProduct) raw
          { «end» := len }
      let rp ← types.RawProduct.Insts.CoreDefaultDefault.default
      let s1 ←
        core.slice.Slice.fill types.RawProduct.Insts.CoreCloneClone s rp
      let i4 ← core.slice.Slice.iter a
      let iter ←
        core.iter.traits.iterator.Iterator.enumerate.trait_default
          (core.iter.traits.iterator.IteratorSliceIter Std.U64) i4
      let raw1 := index_mut_back s1
      let raw2 ←
        poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop0
          fieldBinaryFieldInst backendcontractBulkKernelsInst iter b raw1
      let (s2, index_mut_back1) ←
        core.slice.index.Slice.index_mut
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst
          { «end» := len }
      let (im, iter_mut_back) ← core.slice.Slice.iter_mut s2
      let s3 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice types.RawProduct) raw2
          { «end» := len }
      let (iter1, trait_default_back) ←
        core.iter.traits.iterator.Iterator.zip.trait_default
          (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
          Std.U64)
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
          types.RawProduct) im s3
      let (z, back) ←
        poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop1
          fieldBinaryFieldInst backendcontractBulkKernelsInst iter1
          (fun z1 => z1)
      let z1 := back z
      let im1 := trait_default_back z1
      let s4 := iter_mut_back im1
      let dst1 := index_mut_back1 s4
      let s5 ←
        core.slice.index.Slice.index
          (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst1
          { «end» := len }
      let i5 ← poly.dense.normalized_len s5
      ok (i5, dst1, raw2)

end bulksketch
