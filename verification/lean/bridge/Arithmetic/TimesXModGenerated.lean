-- Original checked Dense modular shift and RangeTo dictionary.
import Arithmetic.TimesXModRuntime

open Aeneas Aeneas.Std Result Error
set_option linter.unusedVariables false

namespace bulksketch

/-- Trait implementation: [core::ops::range::{impl core::ops::range::RangeBounds<T> for core::ops::range::RangeTo<T>}]
    Source: '/rustc/library/core/src/ops/range.rs', lines 1104:0-1104:43
    Name pattern: [core::ops::range::RangeBounds<core::ops::range::RangeTo<@T>, @T>] -/
@[reducible, rust_trait_impl
  "core::ops::range::RangeBounds<core::ops::range::RangeTo<@T>, @T>"]
def core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds (T : Type _) :
  core.ops.range.RangeBounds (core.ops.range.RangeTo T) T := {
  start_bound :=
    core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.start_bound
  end_bound := core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.end_bound
}

/-- [bulksketch::poly::dense::times_x_mod]:
    Source: 'src/poly/dense.rs', lines 234:0-240:1 -/
def poly.dense.times_x_mod
  {F : Type _} {K : Type _} (fieldBinaryFieldInst : field.BinaryField F)
  (backendcontractBulkKernelsInst : backend.contract.BulkKernels K F)
  (coefficients : Slice Std.U64) (modulus : Slice Std.U64) :
  Result (Slice Std.U64)
  := do
  let len := Slice.len coefficients
  let i ← len - 1#usize
  let leading ← Slice.index_usize coefficients i
  let coefficients1 ←
    core.slice.Slice.copy_within
      (core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds Std.Usize)
      core.marker.CopyU64 coefficients { «end» := i } 1#usize
  let coefficients2 ← Slice.update coefficients1 0#usize 0#u64
  let s ←
    core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice
      Std.U64) modulus { «end» := len }
  backendcontractBulkKernelsInst.ArithmeticInst.scale_xor coefficients2 s
    leading

end bulksketch
