import Aeneas

namespace Aeneas.Std.BmLocatorRuntime

open Aeneas.Std Result

open Aeneas.Std.core.iter

def reverseIterator {I Item : Type}
    (dictionary : traits.double_ended.DoubleEndedIterator I Item) :
    traits.iterator.Iterator (adapters.rev.Rev I) Item :=
  { next := adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next dictionary }

/-- The pinned Rust safe RangeInclusive indexing validates the original end
against length, then uses end+1 and the exhausted-start rule. -/
def exclusiveRange (range : core.ops.range.RangeInclusive Usize) :
    Result (core.ops.range.Range Usize) := do
  let stop ← range.end + 1#usize
  .ok ⟨if range.exhausted then stop else range.start, stop⟩

def inclusiveRange (T : Type) :
    core.slice.index.SliceIndex (core.ops.range.RangeInclusive Usize) (Slice T) (Slice T) where
  get range slice := do
    if range.end.val < slice.length then
      let bounds ← exclusiveRange range
      core.slice.index.SliceIndexRangeUsizeSlice.get bounds slice
    else .ok none
  get_mut range slice := do
    if range.end.val < slice.length then
      let bounds ← exclusiveRange range
      core.slice.index.SliceIndexRangeUsizeSlice.get_mut bounds slice
    else .ok (none, fun _ => slice)
  get_unchecked range pointer := do
    let bounds ← exclusiveRange range
    core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked bounds pointer
  get_unchecked_mut range pointer := do
    let bounds ← exclusiveRange range
    core.slice.index.SliceIndexRangeUsizeSlice.get_unchecked_mut bounds pointer
  index range slice := do
    if range.end.val < slice.length then
      let bounds ← exclusiveRange range
      core.slice.index.SliceIndexRangeUsizeSlice.index bounds slice
    else .fail .panic
  index_mut range slice := do
    if range.end.val < slice.length then
      let bounds ← exclusiveRange range
      core.slice.index.SliceIndexRangeUsizeSlice.index_mut bounds slice
    else .fail .panic


end Aeneas.Std.BmLocatorRuntime
