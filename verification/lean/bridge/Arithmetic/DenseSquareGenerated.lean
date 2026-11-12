-- Exact original source declarations. Local notation binds the scoped std runtime.
module
public import Arithmetic.DenseSquareRuntime
public import Arithmetic.DenseNormalizationGenerated
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

local notation "core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT" => Aeneas.Std.DenseSquareRuntime.leftNext
local notation "core.iter.traits.iterator.Iterator.step_by.trait_default" => Aeneas.Std.DenseSquareRuntime.stepBy
local notation "core.iter.traits.iterator.IteratorStepBy" => Aeneas.Std.DenseSquareRuntime.stepNext
local notation "core.iter.traits.iterator.Iterator.zip.trait_default" => Aeneas.Std.DenseSquareRuntime.zip
local notation "core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next" => Aeneas.Std.DenseSquareRuntime.next

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_into]: loop body 0:
    Source: 'src/poly/dense.rs', lines 34:8-36:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_into_loop.body
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
  (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
  (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64) →
  core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
  (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64)) :
  Result (ControlFlow ((core.iter.adapters.zip.Zip
    (core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut Std.U64))
    (core.slice.iter.Iter Std.U64)) × (core.iter.adapters.zip.Zip
    (core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut Std.U64))
    (core.slice.iter.Iter Std.U64) → core.iter.adapters.zip.Zip
    (core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut Std.U64))
    (core.slice.iter.Iter Std.U64))) (core.iter.adapters.zip.Zip
    (core.iter.adapters.step_by.StepBy (core.slice.iter.IterMut Std.U64))
    (core.slice.iter.Iter Std.U64)))
  := do
  let (o, iter1, next_back) ←
    core.iter.adapters.zip.Zip.Insts.CoreIterTraitsIteratorIteratorPair.next
      (core.iter.traits.iterator.IteratorStepBy
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64)) (core.iter.traits.iterator.IteratorSliceIter Std.U64) iter
  match o with
  | none => ok (done (let z := next_back iter1 none
                      back z))
  | some p =>
    let (_, coefficient) := p
    let target ←
      backendcontractBulkKernelsInst.ArithmeticInst.square coefficient
    ok (cont (iter1,
      fun z => let z1 := next_back z (some (target, coefficient))
               back z1))

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_into]: loop 0:
    Source: 'src/poly/dense.rs', lines 34:8-36:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.square_into_loop
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (iter : core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
  (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64))
  (back : core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
  (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64) →
  core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
  (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64)) :
  Result (core.iter.adapters.zip.Zip (core.iter.adapters.step_by.StepBy
    (core.slice.iter.IterMut Std.U64)) (core.slice.iter.Iter Std.U64))
  := do
  loop
    (fun (iter1, back1) =>
      poly.Dense.Insts.BulksketchPolyPolynomial.square_into_loop.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::square_into]:
    Source: 'src/poly/dense.rs', lines 30:4-38:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.square_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Slice Std.U64) (dst : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result (Std.Usize × (Slice Std.U64) × (Slice types.RawProduct))
  := do
  let i := Slice.len a
  let size ← 2#usize * i
  let i1 := Slice.len dst
  massert (i1 >= size)
  let i2 := Slice.len raw
  massert (i2 >= size)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst
      { «end» := size }
  let s1 ← core.slice.Slice.fill core.clone.CloneU64 s 0#u64
  let dst1 := index_mut_back s1
  let (s2, index_mut_back1) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeToUsizeSlice Std.U64) dst1
      { «end» := size }
  let (im, iter_mut_back) ← core.slice.Slice.iter_mut s2
  let (sb, trait_default_back) ←
    core.iter.traits.iterator.Iterator.step_by.trait_default
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64) im 2#usize
  let (iter, trait_default_back1) ←
    core.iter.traits.iterator.Iterator.zip.trait_default
      (core.iter.traits.iterator.IteratorStepBy
      (core.slice.iter.IterMut.Insts.CoreIterTraitsIteratorIteratorMutAT
      Std.U64)) (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter
      Std.U64) sb a
  let back ←
    poly.Dense.Insts.BulksketchPolyPolynomial.square_into_loop
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter (fun z => z)
  let sb1 := trait_default_back1 back
  let im1 := trait_default_back sb1
  let s3 := iter_mut_back im1
  let dst2 := index_mut_back1 s3
  let s4 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) dst2 { «end» := size }
  let i3 ← poly.dense.normalized_len s4
  ok (i3, dst2, raw)

end bulksketch
