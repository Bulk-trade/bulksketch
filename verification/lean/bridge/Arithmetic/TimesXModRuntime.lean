-- Scoped bindings for the original RangeTo copy_within call.
import Arithmetic.SliceKernelTypes

open Aeneas Aeneas.Std Result Error

namespace bulksketch

/-- [core::ops::range::Bound]
    Source: '/rustc/library/core/src/ops/range.rs', lines 710:0-710:17
    Name pattern: [core::ops::range::Bound]
    Visibility: public -/
@[discriminant isize, rust_type "core::ops::range::Bound"]
inductive core.ops.range.Bound (T : Type _) where
| Included : T → core.ops.range.Bound T
| Excluded : T → core.ops.range.Bound T
| Unbounded : core.ops.range.Bound T

/-- Trait declaration: [core::ops::range::RangeBounds]
    Source: '/rustc/library/core/src/ops/range.rs', lines 838:0-838:38
    Name pattern: [core::ops::range::RangeBounds]
    Visibility: public -/
@[rust_trait "core::ops::range::RangeBounds"]
structure core.ops.range.RangeBounds (Self : Type _) (T : Type _) where
  start_bound : Self → Result (core.ops.range.Bound T)
  end_bound : Self → Result (core.ops.range.Bound T)

def core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.start_bound {T : Type}
    (_ : core.ops.range.RangeTo T) : Result (core.ops.range.Bound T) :=
  .ok .Unbounded

def core.ops.range.RangeTo.Insts.CoreOpsRangeRangeBounds.end_bound {T : Type}
    (range : core.ops.range.RangeTo T) : Result (core.ops.range.Bound T) :=
  .ok (.Excluded range.end)

/-- RangeTo copy_within snapshots the original source prefix before
writing the possibly overlapping destination. -/
def core.slice.Slice.copy_within {T : Type}
    (bounds : core.ops.range.RangeBounds (core.ops.range.RangeTo Usize) Usize)
    (_ : core.marker.Copy T) (words : Slice T) (source : core.ops.range.RangeTo Usize)
    (destination : Usize) : Result (Slice T) := do
  let start ← bounds.start_bound source
  let stop ← bounds.end_bound source
  match start, stop with
  | .Unbounded, .Excluded stop =>
    if stop.val ≤ words.length ∧ destination.val + stop.val ≤ words.length then
      .ok (words.setSlice! destination.val (words.val.take stop.val))
    else .fail .panic
  | _, _ => .fail .panic

end bulksketch
