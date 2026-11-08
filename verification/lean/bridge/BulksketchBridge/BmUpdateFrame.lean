import BulksketchBridge.BmUpdateFrameSpec
import BulksketchBridge.BmRuntimeFrames

namespace BulksketchBridge.BmMutable

open Aeneas Aeneas.Std

theorem shift_restore_refines : ActualBmShiftRestore := by
  intro K kernels mul left right delta
  obtain ⟨one, _, two, _⟩ := shifted_xor_loops_refine kernels mul left right 0 id delta (by omega)
  have construct := BmRuntimeFrames.zip_shared_slice_normal (⟨left, 0⟩ : Iter) right
  simp only [core.slice.Slice.iter_mut, Bind.bind, bind_ok]
  try dsimp! only
  change _ = Result.ok (MutableZip.stateAt left right 0, fun later : Zip => later.fst) at construct
  simp only [construct, bind_ok]
  try dsimp! only
  rw [one, two]
  simp only [bind_ok]
  have frame := zipResult_frame left right delta 0 (zipResult left right delta 0 id).1
  have payload := congrArg (fun state : Zip => state.fst.slice) frame
  have restored := congrArg Result.ok payload
  simpa only [zipResult, MutableZip.stateAt, Nat.sub_zero] using And.intro restored restored

theorem scale_restore_refines : ActualBmScaleRestore := by
  intro K kernels mul left scale
  obtain ⟨one, two, three, four⟩ := scale_loops_refine kernels mul left 0 id scale (by omega)
  simp only [bulksketch.MutASlice.Insts.CoreIterTraitsCollectIntoIteratorMutATIterMut.into_iter,
    core.slice.Slice.iter_mut, Bind.bind, bind_ok]
  try dsimp! only
  rw [one, two, three, four]
  simp [bind_ok, iterResult, iter_writeback]

end BulksketchBridge.BmMutable
