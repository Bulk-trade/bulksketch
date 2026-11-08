-- Original exact division with its explicit checked div/rem application slot.
import Arithmetic.SliceKernelTypes
import Arithmetic.RebuiltLfsrRuntime

open Aeneas Aeneas.Std Result Error

namespace Aeneas.Std.DenseDivisionRuntime

abbrev DivRem := ∀ {F K : Type}, bulksketch.field.BinaryField F →
    bulksketch.backend.contract.BulkKernels K F →
    Slice U64 → Slice U64 → Slice U64 → Slice U64 → Slice bulksketch.types.RawProduct →
    Result ((Usize × Usize) × Slice U64 × Slice U64 × Slice bulksketch.types.RawProduct)

end Aeneas.Std.DenseDivisionRuntime

namespace bulksketch

variable (division : Aeneas.Std.DenseDivisionRuntime.DivRem)
local notation "poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into" => division
local notation "core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice" =>
  RebuiltLfsrRuntime.inclusive

/-- [bulksketch::poly::dense::{impl bulksketch::poly::Polynomial<F, K> for bulksketch::poly::Dense}::exact_divide_into]:
    Source: 'src/poly/dense.rs', lines 98:4-111:5 -/
def poly.Dense.Insts.BulksketchPolyPolynomial.exact_divide_into
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (a : Slice Std.U64) (b : Slice Std.U64) (q : Slice Std.U64)
  (rem : Slice Std.U64) (raw : Slice types.RawProduct) :
  Result ((Option Std.Usize) × (Slice Std.U64) × (Slice Std.U64) × (Slice
    types.RawProduct))
  := do
  let ((q_len, rem_len), q1, rem1, raw1) ←
    poly.Dense.Insts.BulksketchPolyPolynomial.div_rem_into fieldBinaryFieldInst
      backendcontractBulkKernelsInst a b q rem raw
  if rem_len != 0#usize
  then
    let i := Slice.len a
    let (s, index_mut_back) ←
      core.slice.index.Slice.index_mut
        (core.ops.range.RangeToInclusiveUsize.Insts.CoreSliceIndexSliceIndexSliceSlice
        Std.U64) q1 { «end» := i }
    let s1 ← core.slice.Slice.fill core.clone.CloneU64 s 0#u64
    let q2 := index_mut_back s1
    ok (none, q2, rem1, raw1)
  else ok (some q_len, q1, rem1, raw1)

end bulksketch
