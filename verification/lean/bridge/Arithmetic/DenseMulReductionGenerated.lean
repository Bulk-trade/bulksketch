-- Exact original final-reduction loop declarations. Imports are adapted only.
module
public import Arithmetic.MutableZipRuntime
public import Arithmetic.SliceKernelTypes
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
namespace bulksketch

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]: loop body 2:
    Source: 'src/poly/dense.rs', lines 24:8-26:9 -/
@[rust_loop_body]
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop1.body
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

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::mul_into]: loop 2:
    Source: 'src/poly/dense.rs', lines 24:8-26:9 -/
@[rust_loop]
def poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop1
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
      poly.Dense.Insts.BulksketchPolyPolynomial.mul_into_loop1.body
      fieldBinaryFieldInst backendcontractBulkKernelsInst iter1 back1)
    (iter, back)

end bulksketch
