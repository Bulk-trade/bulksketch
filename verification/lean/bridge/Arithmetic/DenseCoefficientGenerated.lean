-- Exact original-source declaration projection. Imports are adapted only.
module
public import Arithmetic.SliceKernelTypes
public import Arithmetic.DenseNormalizationGenerated
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
noncomputable section
namespace bulksketch

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::xor_coefficient]:
    Source: 'src/poly/dense.rs', lines 159:4-165:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.xor_coefficient
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (dst : Slice Std.U64) (len : Std.Usize) (index : Std.Usize) (value : Std.U64)
  :
  Result (Std.Usize × (Slice Std.U64))
  := do
  let i := Slice.len dst
  massert (len <= i)
  let i1 := Slice.len dst
  massert (index < i1)
  let i2 ← index + 1#usize
  let size ← lift (core.cmp.impls.OrdUsize.max len i2)
  let (s, index_mut_back) ←
    core.slice.index.Slice.index_mut
      (core.slice.index.SliceIndexRangeUsizeSlice Std.U64) dst
      { start := len, «end» := size }
  let s1 ← core.slice.Slice.fill core.clone.CloneU64 s 0#u64
  let dst1 := index_mut_back s1
  let i3 ← Slice.index_usize dst1 index
  let i4 ← lift (i3 ^^^ value)
  let dst2 ← Slice.update dst1 index i4
  let s2 ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) dst2 { «end» := size }
  let i5 ← poly.dense.normalized_len s2
  ok (i5, dst2)

end bulksketch
