import BulksketchBridge.BmUpdateFrame

namespace BulksketchBridge.BmConnectionUpdate

open Aeneas Aeneas.Std BmMutable DenseCoefficient RebuiltLfsr
open bulksketch.backend.contract bulksketch.decode.bm

/-- The original nonzero-discrepancy connection subcomputation, with the
projected standard-library bindings and all three slice writebacks. -/
def run {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (connection previous : Slice U64) (len nextDegree shift previousLen : Usize)
    (previousDelta delta : U64) : Result (Slice U64) := do
  let (head, restorePrefix) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeToUsizeSlice U64) connection { «end» := len }
  let (iter, restoreIter) ←
    bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter head
  let (final, back) ← locator_loop0_loop2 fieldDictionary kernels iter (fun later => later) previousDelta
  let scaled := restorePrefix (restoreIter (back final))
  let range ← core.ops.range.RangeInclusive.new len nextDegree
  let (gap, restoreGap) ← core.slice.index.Slice.index_mut
    (BmLocatorRuntime.inclusiveRange U64) scaled range
  let zeros ← core.slice.Slice.fill core.clone.CloneU64 gap 0#u64
  let filled := restoreGap zeros
  let stop ← shift + previousLen
  let (window, restoreWindow) ← core.slice.index.Slice.index_mut
    (core.slice.index.SliceIndexRangeUsizeSlice U64) filled { start := shift, «end» := stop }
  let (left, restoreLeft) ← core.slice.Slice.iter_mut window
  let right ← core.slice.index.Slice.index
    (core.slice.index.SliceIndexRangeToUsizeSlice U64) previous { «end» := previousLen }
  let (zipped, restoreZipped) ← Aeneas.Std.MutableZip.construct
    (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) left right
  let (finalZip, backZip) ← locator_loop0_loop3 fieldDictionary kernels zipped (fun later => later) delta
  .ok (restoreWindow (restoreLeft (restoreZipped (backZip finalZip))))

def scaledConnection (connection : Slice U64) (len : Nat) (scale : U64) : Slice U64 :=
  let head := prefixSlice connection len
  connection.setSlice! 0 (patchWords (fun i => mulWord scale head[i]!) 0 head.length head).val

def clearedConnection (scaled : Slice U64) (len nextDegree : Nat) : Slice U64 :=
  scaled.setSlice! len (zeroWords (ClosedLeaf.region scaled len (nextDegree + 1))).val

def expectedConnection (connection previous : Slice U64) (len nextDegree shift previousLen : Nat)
    (previousDelta delta : U64) : Slice U64 :=
  let cleared := clearedConnection (scaledConnection connection len previousDelta) len nextDegree
  let left := ClosedLeaf.region cleared shift (shift + previousLen)
  let right := prefixSlice previous previousLen
  cleared.setSlice! shift (patchWords (fun i => shiftedWord delta left[i]! right[i]!)
    0 (min left.length right.length) left).val

theorem connection_update_refines {K : Type} (kernels : BulkKernels K bulksketch.field.Gf64)
    (mul : NativeMul kernels) (connection previous : Slice U64)
    (len nextDegree shift previousLen : Usize) (previousDelta delta : U64)
    (prefixBound : len.val ≤ connection.length)
    (gapOrdered : len.val ≤ nextDegree.val + 1)
    (gapBound : nextDegree.val < connection.length)
    (shiftedBound : shift.val + previousLen.val ≤ connection.length)
    (previousBound : previousLen.val ≤ previous.length) :
    run kernels connection previous len nextDegree shift previousLen previousDelta delta =
      .ok (expectedConnection connection previous len.val nextDegree.val shift.val previousLen.val
        previousDelta delta) := by
  have prefixNormal := RebuiltLfsr.prefix_normal connection len prefixBound
  let head := prefixSlice connection len.val
  have scaled := (scale_loops_refine kernels mul head 0 id previousDelta (Nat.zero_le _)).1
  have scalePatch :
      ((iterResult head (mulWord previousDelta) 0 id).2
        (iterResult head (mulWord previousDelta) 0 id).1).slice =
      patchWords (fun i => mulWord previousDelta head[i]!) 0 head.length head := by
    simpa only [iterResult, id_eq, Nat.sub_zero] using
      congrArg (fun iter : Iter => iter.slice)
        (iter_writeback (fun i => mulWord previousDelta head[i]!) 0 head.length ⟨head, head.length⟩)
  let c1 := scaledConnection connection len.val previousDelta
  have c1Exact :
      restorePrefix connection (patchWords (fun i => mulWord previousDelta head[i]!) 0 head.length head) = c1 := by
    apply Slice.ext
    rfl
  have c1Length : c1.length = connection.length := by
    exact Slice.setSlice!_length _ _ _
  have gapNormal := BmRuntimeFrames.inclusive_mutable_new c1 len nextDegree gapOrdered
    (by rw [c1Length]; exact gapBound)
  let c2 := clearedConnection c1 len.val nextDegree.val
  have c2Length : c2.length = connection.length := by
    unfold c2 clearedConnection
    rw [Slice.setSlice!_length, c1Length]
  have stopFits : shift.val + previousLen.val ≤ Usize.max :=
    Nat.le_trans shiftedBound (Slice.length_ineq connection)
  obtain ⟨stop, stopNormal, stopValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := shift) (y := previousLen) stopFits)
  have leftNormal := ClosedLeaf.mutable_region_normal c2 shift stop (by omega) (by omega)
  have rightNormal := RebuiltLfsr.shared_prefix_normal previous previousLen previousBound
  let left := ClosedLeaf.region c2 shift.val stop.val
  let right := prefixSlice previous previousLen.val
  have zipped := BmRuntimeFrames.zip_shared_slice_normal (⟨left, 0⟩ : Iter) right
  change _ = Result.ok (MutableZip.stateAt left right 0, fun later : Zip => later.fst) at zipped
  have shifted := (shifted_xor_loops_refine kernels mul left right 0 id delta (Nat.zero_le _)).1
  have shiftedPatch := zipResult_frame left right delta 0 (zipResult left right delta 0 id).1
  unfold run
  simp only [Slice.index_mut_SliceIndexRangeToUsizeSliceInst, prefixNormal, bind_ok,
    bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    core.slice.Slice.iter_mut]
  dsimp! only
  change Aeneas.Std.bind
    (locator_loop0_loop2 fieldDictionary kernels ⟨head, 0⟩ id previousDelta) _ = _
  simp only [scaled, bind_ok]
  dsimp! only
  simp only [scalePatch, c1Exact, core.ops.range.RangeInclusive.new, bind_ok]
  simp only [core.slice.index.Slice.index_mut, gapNormal, bind_ok]
  dsimp! only
  simp only [RebuiltLfsr.fill_zero, bind_ok, stopNormal]
  change Aeneas.Std.bind
    (core.slice.index.SliceIndexRangeUsizeSlice.index_mut ⟨shift, stop⟩ c2) _ = _
  simp only [leftNormal, Slice.index_SliceIndexRangeToUsizeSliceInst, rightNormal, bind_ok]
  dsimp! only
  change Aeneas.Std.bind
    (Aeneas.Std.MutableZip.construct
      (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter U64) (⟨left, 0⟩ : Iter) right) _ = _
  simp only [zipped, bind_ok]
  dsimp! only
  change Aeneas.Std.bind
    (locator_loop0_loop3 fieldDictionary kernels (MutableZip.stateAt left right 0) id delta) _ = _
  simp only [shifted, bind_ok]
  dsimp! only
  rw [shiftedPatch]
  change Result.ok (c2.setSlice! shift.val
    (patchWords (fun i => shiftedWord delta left[i]! right[i]!) 0 (min left.length right.length) left).val) = _
  have leftExact : left = ClosedLeaf.region c2 shift.val (shift.val + previousLen.val) := by
    unfold left
    rw [stopValue]
  rw [leftExact]
  rfl


end BulksketchBridge.BmConnectionUpdate
