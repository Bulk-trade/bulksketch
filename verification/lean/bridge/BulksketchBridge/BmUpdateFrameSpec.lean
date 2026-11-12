import BulksketchBridge.BmMutableFrames
import BulksketchBridge.BmRuntimeFramesSpec

namespace BulksketchBridge.BmMutable

open Aeneas.Std
open bulksketch.backend.contract bulksketch.decode.bm

/-- Both original nonzero-discrepancy loops, with the two actual mutable
writeback calls applied to the original forward result. -/
def ActualBmShiftRestore : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), NativeMul kernels →
    ∀ (left right : Slice U64) (delta : U64),
      let expected := patchWords (fun index => shiftedWord delta left[index]! right[index]!)
        0 (min left.length right.length) left
      (do
        let (im, restoreSlice) ← core.slice.Slice.iter_mut left
        let (z, restoreIter) ← Aeneas.Std.MutableZip.construct
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) im right
        let (final, back) ← locator_loop0_loop3 fieldDictionary kernels z id delta
        .ok (restoreSlice (restoreIter (back final)))) = .ok expected ∧
      (do
        let (im, restoreSlice) ← core.slice.Slice.iter_mut left
        let (z, restoreIter) ← Aeneas.Std.MutableZip.construct
          (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) im right
        let (final, back) ← locator_loop0_loop8 fieldDictionary kernels z id delta
        .ok (restoreSlice (restoreIter (back final)))) = .ok expected

/-- The original four scale loops restore the entire prefix slice through
the actual mutable IntoIterator writeback. -/
def ActualBmScaleRestore : Prop :=
  ∀ {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64), NativeMul kernels →
    ∀ (left : Slice U64) (scale : U64),
      let expected := patchWords (fun index => mulWord scale left[index]!) 0 left.length left
      (do
        let (im, restoreSlice) ← bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter left
        let (final, back) ← locator_loop0_loop2 fieldDictionary kernels im id scale
        .ok (restoreSlice (back final))) = .ok expected ∧
      (do
        let (im, restoreSlice) ← bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter left
        let (final, back) ← locator_loop0_loop4 fieldDictionary kernels im id scale
        .ok (restoreSlice (back final))) = .ok expected ∧
      (do
        let (im, restoreSlice) ← bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter left
        let (final, back) ← locator_loop0_loop7 fieldDictionary kernels im id scale
        .ok (restoreSlice (back final))) = .ok expected ∧
      (do
        let (im, restoreSlice) ← bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter left
        let (final, back) ← locator_loop0_loop9 fieldDictionary kernels im id scale
        .ok (restoreSlice (back final))) = .ok expected

end BulksketchBridge.BmMutable
