-- Original unoutlined Dense division. The checked scoped translator is pinned in extraction/dense-div-rem.
import Arithmetic.DenseReducerSquareGenerated

open Aeneas Aeneas.Std Result ControlFlow Error

namespace bulksketch

set_option linter.dupNamespace false
set_option linter.unusedVariables false

local notation "core.slice.Slice.last" => DenseReducerTableRuntime.last

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 0:
    Source: 'src/poly/dense.rs', lines 57:8-62:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop0.body
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
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      types.RawProduct) (core.iter.traits.iterator.IteratorSliceIter Std.U64)
      iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (_, coefficient) := p
    ok (cont (iter1,
      fun z =>
        let z1 :=
          next_back z (some ({ lo := coefficient, hi := 0#u64 }, coefficient))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 0:
    Source: 'src/poly/dense.rs', lines 57:8-62:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop0
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop0.body iter1
      back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 2:
    Source: 'src/poly/dense.rs', lines 77:16-79:17 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop0.body
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
    let (slot, coefficient) := p
    let i ← lift (slot.lo ^^^ coefficient)
    ok (cont (iter1,
      fun z =>
        let z1 := next_back z (some ({ slot with lo := i }, coefficient))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 2:
    Source: 'src/poly/dense.rs', lines 77:16-79:17 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop0
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop0.body
      iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 3:
    Source: 'src/poly/dense.rs', lines 82:12-86:13 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (factor : Std.U64)
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
    let (slot, coefficient) := p
    let product ←
      backendcontractBulkKernelsInst.ArithmeticInst.raw_mul factor coefficient
    let i ← lift (slot.lo ^^^ product.lo)
    let i1 ← lift (slot.hi ^^^ product.hi)
    ok (cont (iter1,
      fun z =>
        let z1 := next_back z (some ({ lo := i, hi := i1 }, coefficient))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 3:
    Source: 'src/poly/dense.rs', lines 82:12-86:13 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64))
  (factor : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst factor iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 4:
    Source: 'src/poly/dense.rs', lines 77:16-79:17 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop2.body
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
    let (slot, coefficient) := p
    let i ← lift (slot.lo ^^^ coefficient)
    ok (cont (iter1,
      fun z =>
        let z1 := next_back z (some ({ slot with lo := i }, coefficient))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 4:
    Source: 'src/poly/dense.rs', lines 77:16-79:17 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop2
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop2.body
      iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 5:
    Source: 'src/poly/dense.rs', lines 82:12-86:13 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop3.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (factor : Std.U64)
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
    let (slot, coefficient) := p
    let product ←
      backendcontractBulkKernelsInst.ArithmeticInst.raw_mul factor coefficient
    let i ← lift (slot.lo ^^^ product.lo)
    let i1 ← lift (slot.hi ^^^ product.hi)
    ok (cont (iter1,
      fun z =>
        let z1 := next_back z (some ({ lo := i, hi := i1 }, coefficient))
        back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 5:
    Source: 'src/poly/dense.rs', lines 82:12-86:13 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop3
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
  (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
  (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64))
  (factor : Std.U64) :
  Result ((core.iter.adapters.zip.Zip (core.slice.iter.IterMut
    types.RawProduct) (core.slice.iter.Iter Std.U64)) ×
    (core.iter.adapters.zip.Zip (core.slice.iter.IterMut types.RawProduct)
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.slice.iter.IterMut types.RawProduct) (core.slice.iter.Iter Std.U64)))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop3.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst factor iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 1:
    Source: 'src/poly/dense.rs', lines 66:8-87:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (b : Slice Std.U64) (inverse : Std.U64) (degree : Std.Usize)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (q : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result (ControlFlow ((core.iter.adapters.rev.Rev (core.ops.range.Range
    Std.Usize)) × (Slice Std.U64) × (Slice types.RawProduct)) ((Slice
    Std.U64) × (Slice types.RawProduct)))
  := do
  let (o, iter1) ←
    core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) iter
  match o with
  | none => ok (done (q, raw))
  | some top =>
    let rp ← Slice.index_usize raw top
    let factor ← backendcontractBulkKernelsInst.ArithmeticInst.reduce rp
    if inverse != 1#u64
    then
      let factor1 ←
        backendcontractBulkKernelsInst.ArithmeticInst.mul factor inverse
      let offset ← top - degree
      let (_, index_mut_back) ← Slice.index_mut_usize q offset
      if factor1 = 0#u64
      then let s := index_mut_back factor1
           ok (cont (iter1, s, raw))
      else
        if factor1 = 1#u64
        then
          let (s, index_mut_back1) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice types.RawProduct) raw
              { start := offset, «end» := top }
          let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) b
              { «end» := degree }
          let (iter2, trait_default_back) ←
            core.iter.traits.iterator.Iterator.zip.trait_default
              (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
              types.RawProduct)
              (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
              Std.U64) im s1
          let (z, back) ←
            poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop0
              iter2 (fun z1 => z1)
          let z1 := back z
          let im1 := trait_default_back z1
          let s2 := iter_mut_back im1
          let s3 := index_mut_back1 s2
          let s4 := index_mut_back factor1
          ok (cont (iter1, s4, s3))
        else
          let (s, index_mut_back1) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice types.RawProduct) raw
              { start := offset, «end» := top }
          let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) b
              { «end» := degree }
          let (iter2, trait_default_back) ←
            core.iter.traits.iterator.Iterator.zip.trait_default
              (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
              types.RawProduct)
              (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
              Std.U64) im s1
          let (z, back) ←
            poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop1
              fieldBinaryFieldInst backendcontractBulkKernelsInst iter2
              (fun z1 => z1) factor1
          let z1 := back z
          let im1 := trait_default_back z1
          let s2 := iter_mut_back im1
          let s3 := index_mut_back1 s2
          let s4 := index_mut_back factor1
          ok (cont (iter1, s4, s3))
    else
      let offset ← top - degree
      let (_, index_mut_back) ← Slice.index_mut_usize q offset
      if factor = 0#u64
      then let s := index_mut_back factor
           ok (cont (iter1, s, raw))
      else
        if factor = 1#u64
        then
          let (s, index_mut_back1) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice types.RawProduct) raw
              { start := offset, «end» := top }
          let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) b
              { «end» := degree }
          let (iter2, trait_default_back) ←
            core.iter.traits.iterator.Iterator.zip.trait_default
              (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
              types.RawProduct)
              (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
              Std.U64) im s1
          let (z, back) ←
            poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop2
              iter2 (fun z1 => z1)
          let z1 := back z
          let im1 := trait_default_back z1
          let s2 := iter_mut_back im1
          let s3 := index_mut_back1 s2
          let s4 := index_mut_back factor
          ok (cont (iter1, s4, s3))
        else
          let (s, index_mut_back1) ←
            core.slice.index.Slice.index_mut
              (core.slice.index.SliceIndexRangeUsizeSlice types.RawProduct) raw
              { start := offset, «end» := top }
          let (im, iter_mut_back) ← core.slice.Slice.iter_mut s
          let s1 ←
            core.slice.index.Slice.index
              (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) b
              { «end» := degree }
          let (iter2, trait_default_back) ←
            core.iter.traits.iterator.Iterator.zip.trait_default
              (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
              types.RawProduct)
              (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
              Std.U64) im s1
          let (z, back) ←
            poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1_loop3
              fieldBinaryFieldInst backendcontractBulkKernelsInst iter2
              (fun z1 => z1) factor
          let z1 := back z
          let im1 := trait_default_back z1
          let s2 := iter_mut_back im1
          let s3 := index_mut_back1 s2
          let s4 := index_mut_back factor
          ok (cont (iter1, s4, s3))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 1:
    Source: 'src/poly/dense.rs', lines 66:8-87:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.rev.Rev (core.ops.range.Range Std.Usize))
  (b : Slice Std.U64) (q : Slice Std.U64) (raw : Slice types.RawProduct)
  (inverse : Std.U64) (degree : Std.Usize) :
  Result ((Slice Std.U64) × (Slice types.RawProduct))
  := do
  loop
    (fun (iter1, q1, raw1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst b inverse degree
      iter1 q1 raw1)
    (iter, q, raw)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop body 6:
    Source: 'src/poly/dense.rs', lines 89:8-91:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop2.body
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

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]: loop 6:
    Source: 'src/poly/dense.rs', lines 89:8-91:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop2
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
      poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop2.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::div_rem_into]:
    Source: 'src/poly/dense.rs', lines 40:4-96:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Slice Std.U64) (b : Slice Std.U64) (q : Slice Std.U64)
  (rem : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result ((Std.Usize × Std.Usize) × (Slice Std.U64) × (Slice Std.U64) ×
    (Slice types.RawProduct))
  := do
  let o ← core.slice.Slice.last b
  let leading ← core.option.Option.expect o (toStr "zero polynomial divisor")
  let inverse ←
    if leading = 1#u64
    then ok 1#u64
    else
      do
      let o1 ← backendcontractBulkKernelsInst.ArithmeticInst.inverse leading
      core.option.Option.expect o1 (toStr "noncanonical polynomial divisor")
  let i := Slice.len a
  let size ← i + 1#usize
  let i1 := Slice.len q
  massert (i1 >= size)
  let i2 := Slice.len rem
  massert (i2 >= size)
  let i3 := Slice.len raw
  massert (i3 >= size)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) q
      { «end» := size }
  let s1 ← core.slice.Slice.fill core.clone.CloneU64 s 0#u64
  let (s2, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rem
      { «end» := size }
  let s3 ← core.slice.Slice.fill core.clone.CloneU64 s2 0#u64
  let i4 := Slice.len a
  let (s4, index_mut_back2) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice types.RawProduct) raw
      { «end» := i4 }
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut s4
  let (iter, trait_default_back) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      types.RawProduct)
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter Std.U64)
      im a
  let rem1 := index_mut_back1 s3
  let q1 := index_mut_back s1
  let back ←
    poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop0 iter
      (fun z => z)
  let i5 := Slice.len b
  let degree ← i5 - 1#usize
  let i6 := Slice.len a
  let iter1 ←
    core.iter.traits.iterator.Iterator.rev.trait_default
      (core.iter.traits.iterator.IteratorRange core.iter.range.StepUsize)
      (core.ops.range.Range.Insts.DoubleEndedIterator
      core.iter.range.StepUsize) { start := degree, «end» := i6 }
  let im1 := trait_default_back back
  let s5 := iter_mut_back im1
  let raw1 := index_mut_back2 s5
  let (q2, raw2) ←
    poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop1
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 b q1 raw1
      inverse degree
  let i7 := Slice.len a
  let remainder_size ← lift (core.cmp.impls.OrdUsize.min degree i7)
  let (s6, index_mut_back3) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) rem1
      { «end» := remainder_size }
  let (im2, iter_mut_back1) ← core.slice.Slice.iter_mut s6
  let i8 ← core.slice.Slice.iter raw2
  let (iter2, trait_default_back1) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) (core.iter.traits.collect.IntoIterator.Blanket
      (core.iter.traits.iterator.IteratorSliceIter types.RawProduct)) im2 i8
  let (z, back1) ←
    poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into_loop2
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter2 (fun z1 => z1)
  let s7 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) q2 { «end» := size }
  let i9 ← poly.dense.normalized_len s7
  let z1 := back1 z
  let im3 := trait_default_back1 z1
  let s8 := iter_mut_back1 im3
  let rem2 := index_mut_back3 s8
  let s9 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) rem2 { «end» := remainder_size }
  let i10 ← poly.dense.normalized_len s9
  ok ((i9, i10), q2, rem2, raw2)

end bulksketch
