import Arithmetic.BmLocatorRuntime
import BulksketchBridge.ClosedLeafWindows
import Arithmetic.MutableZipRuntime

namespace BulksketchBridge.BmRuntimeFrames

open Aeneas.Std

abbrev InclusiveRange := core.ops.range.RangeInclusive Usize

def startIndex (range : InclusiveRange) : Nat :=
  if range.exhausted then range.end.val + 1 else range.start.val

def RangeAdmitted (words : Slice U64) (range : InclusiveRange) : Prop :=
  range.end.val < words.length ∧ startIndex range ≤ range.end.val + 1

def InclusiveSharedRefines : Prop :=
  ∀ (words : Slice U64) (range : InclusiveRange), RangeAdmitted words range →
    (BmLocatorRuntime.inclusiveRange U64).index range words =
      Result.ok (ClosedLeaf.region words (startIndex range) (range.end.val + 1))

/-- The callback describes every replacement in the pinned total model. -/
def InclusiveMutableRefines : Prop :=
  ∀ (words : Slice U64) (range : InclusiveRange), RangeAdmitted words range →
    (BmLocatorRuntime.inclusiveRange U64).index_mut range words =
      Result.ok (ClosedLeaf.region words (startIndex range) (range.end.val + 1),
        fun replacement => words.setSlice! (startIndex range) replacement.val)

/-- Replacements of the accessed length write exactly the indexed words. -/
def BackwardFrame (words : Slice U64) (start stop : Nat)
    (back : Slice U64 → Slice U64) : Prop :=
  ∀ replacement, replacement.length = stop - start →
    (back replacement).length = words.length ∧
    ∀ index, index < words.length →
      (back replacement)[index]! =
        if start ≤ index ∧ index < stop then replacement[index - start]! else words[index]!

def InclusiveWritebackRefines : Prop :=
  ∀ (words : Slice U64) (range : InclusiveRange), RangeAdmitted words range →
    ∃ window back, (BmLocatorRuntime.inclusiveRange U64).index_mut range words = Result.ok (window, back) ∧
      window = ClosedLeaf.region words (startIndex range) (range.end.val + 1) ∧
      BackwardFrame words (startIndex range) (range.end.val + 1) back

def ZipIteratorRefines : Prop :=
  ∀ {A B : Type} (left : core.slice.iter.IterMut A) (right : core.slice.iter.Iter B),
    Aeneas.Std.MutableZip.construct
      (core.iter.traits.collect.IntoIterator.Blanket (core.iter.traits.iterator.IteratorSliceIter B))
      left right =
        Result.ok ((⟨left, right⟩ : Aeneas.Std.MutableZip.State A B),
          fun later : Aeneas.Std.MutableZip.State A B => later.fst)

def ZipSharedSliceRefines : Prop :=
  ∀ {A B : Type} (left : core.slice.iter.IterMut A) (right : Slice B),
    Aeneas.Std.MutableZip.construct
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter B) left right =
        Result.ok ((⟨left, ⟨right, 0⟩⟩ : Aeneas.Std.MutableZip.State A B),
          fun later : Aeneas.Std.MutableZip.State A B => later.fst)

end BulksketchBridge.BmRuntimeFrames
