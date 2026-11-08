module
public import Arithmetic.RebuiltLfsrTypes
@[expose] public section

namespace Aeneas.Std.RebuiltLfsrRuntime

open Result

/-- The safe inclusive prefix converts to an exclusive endpoint after
checking that its last index is in bounds. Raw pointer methods inherit the
pinned RangeTo model, which leaves their memory semantics undefined. -/
def inclusive (T : Type) :
    core.slice.index.SliceIndex (bulksketch.core.ops.range.RangeToInclusive Usize) (Slice T) (Slice T) where
  get range slice := do
    if range.end.val < slice.length then
      let stop ← range.end + 1#usize
      core.slice.index.SliceIndexRangeToUsizeSlice.get ⟨stop⟩ slice
    else ok none
  get_mut range slice := do
    if range.end.val < slice.length then
      let stop ← range.end + 1#usize
      core.slice.index.SliceIndexRangeToUsizeSlice.get_mut ⟨stop⟩ slice
    else ok (none, fun _ => slice)
  get_unchecked _ pointer :=
    core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked ⟨0#usize⟩ pointer
  get_unchecked_mut _ pointer :=
    core.slice.index.SliceIndexRangeToUsizeSlice.get_unchecked_mut ⟨0#usize⟩ pointer
  index range slice := do
    if range.end.val < slice.length then
      let stop ← range.end + 1#usize
      core.slice.index.SliceIndexRangeToUsizeSlice.index ⟨stop⟩ slice
    else fail .panic
  index_mut range slice := do
    if range.end.val < slice.length then
      let stop ← range.end + 1#usize
      core.slice.index.SliceIndexRangeToUsizeSlice.index_mut ⟨stop⟩ slice
    else fail .panic

def mutableSharedNe {A B : Type} (equality : core.cmp.PartialEq A B)
    (left : A) (right : B) : Result Bool :=
  equality.ne left right

def mutableIntoIter {T : Type} (slice : Slice T) :
    Result (core.slice.iter.IterMut T × (core.slice.iter.IterMut T → Slice T)) :=
  core.slice.Slice.iter_mut slice

end Aeneas.Std.RebuiltLfsrRuntime
