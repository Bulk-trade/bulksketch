import BulksketchBridge.AvxSliceKernelWords
import BulksketchBridge.AvxSquareScalarMemory

namespace BulksketchBridge.AvxSliceKernel

open Aeneas.Std Aeneas.Std.Avx512Register Aeneas.Std.AvxSquareRuntime
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 2700000

def writeBlock (op : Operation) (dst src : Slice U64) (offset : Nat) : Slice U64 :=
  dst.setSlice! offset (blockWords op.kernel (pairAt dst src offset offset)).val

@[simp] theorem block_write_length (op : Operation) (dst src : Slice U64) (offset : Nat) :
    (writeBlock op dst src offset).length = dst.length := Slice.setSlice!_length ..

/-- The original square block reads only its source. The original
nontrivial scale block reads the destination and source before the store.
Every read/write is the exact masked-memory LLBC on a finite address. -/
structure AllocatedBlock (op : Operation) (dstBase srcBase : Address) (permit : Address → Bool)
    (dst src : Slice U64) (offset stop : Nat) (heap updated : AddressHeap) : Prop where
  source :
    let region := ClosedLeaf.region src offset stop
    let address := srcBase + BitVec.ofNat 64 (8 * offset)
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨address.toNat, region.len⟩) =
      some (.register (loadWords region), liftHeap heap)
  destination :
    match op with
    | .square => True
    | .scale _ =>
      let region := ClosedLeaf.region dst offset stop
      let address := dstBase + BitVec.ofNat 64 (8 * offset)
      exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨address.toNat, region.len⟩) =
        some (.register (loadWords region), liftHeap heap)
  store :
    let region := ClosedLeaf.region dst offset stop
    let address := dstBase + BitVec.ofNat 64 (8 * offset)
    exec (liftPermission permit) storeProgram
      (storeInput (liftHeap heap) ⟨address.toNat, region.len⟩
        (register op.kernel region (ClosedLeaf.region src offset stop))) =
      some (.unit, liftHeap updated)
  frame :
    ∀ address, address.toNat < dstBase.toNat + 8 * offset ∨ dstBase.toNat + 8 * stop ≤ address.toNat →
      updated address = heap address

theorem allocated_slice_block (op : Operation) (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (permit : Address → Bool) (dstBase srcBase : Address) (dst src : Slice U64) (offset : Nat)
    (same : dst.length = src.length) (active : offset < dst.length)
    (dstView : WriteView live la57 heap permit dstBase (8 * dst.length) 8)
    (dstBytes : FiniteWordWindow heap dstBase dst.length (fun i => dst[i]!.bv))
    (srcView : ReadView live la57 heap srcBase (8 * src.length) 8)
    (srcBytes : FiniteWordWindow heap srcBase src.length (fun i => src[i]!.bv)) :
    let written := writeBlock op dst src offset
    ∃ updated, AllocatedBlock op dstBase srcBase permit dst src offset (stopAt dst offset) heap updated ∧
      FiniteWordWindow updated dstBase dst.length (fun i => written[i]!.bv) ∧
      WriteView live la57 updated permit dstBase (8 * dst.length) 8 ∧
      FramesOutside heap updated dstBase (8 * dst.length) := by
  let stop := stopAt dst offset
  have ordered : offset < stop := by unfold stop stopAt; omega
  have bound : stop ≤ dst.length := Nat.min_le_right _ _
  have width : stop - offset ≤ 8 := by unfold stop stopAt; omega
  have srcRead := load_allocated_window live la57 heap srcBase src permit offset stop ordered
    (bound.trans_eq same) width srcView srcBytes
  have dstRead := load_allocated_window live la57 heap dstBase dst permit offset stop ordered
    bound width dstView.toReadView dstBytes
  let reg := register op.kernel (ClosedLeaf.region dst offset stop) (ClosedLeaf.region src offset stop)
  obtain ⟨updated, write, words, frame⟩ :=
    store_allocated_window live la57 heap dstBase dst permit reg offset stop ordered bound width dstView dstBytes
  have dstFits : (ClosedLeaf.region dst offset stop).length ≤ 8 := by
    rw [ClosedLeaf.region_length _ _ _ bound]
    exact width
  have srcChunk : chunk (pairAt dst src offset offset).snd = ClosedLeaf.region src offset stop := by
    change ClosedLeaf.region src offset (stopAt src offset) = _
    simp only [stop, stopAt, same]
  have writtenEq : writeBlock op dst src offset =
      dst.setSlice! offset (storeWords (ClosedLeaf.region dst offset stop) reg dstFits).val := by
    unfold writeBlock blockWords
    change dst.setSlice! offset
      ((if fits : (ClosedLeaf.region dst offset stop).length ≤ 8 then
          storeWords (ClosedLeaf.region dst offset stop)
            (register op.kernel (ClosedLeaf.region dst offset stop) (chunk (pairAt dst src offset offset).snd)) fits
        else ClosedLeaf.region dst offset stop).val) = _
    rw [dite_eq_left dstFits, srcChunk]
  have exactBytes : FiniteWordWindow updated dstBase dst.length (fun i => (writeBlock op dst src offset)[i]!.bv) := by
    rw [writtenEq]
    exact words
  refine ⟨updated, ⟨srcRead, ?_, write, frame⟩, exactBytes,
    write_view_from_words dstView _ exactBytes, ?_⟩
  · split
    · trivial
    · exact dstRead
  · intro address outside
    exact frame address (by omega)

def Prefix (op : Operation) (original src current : Slice U64) (offset : Nat) : Prop :=
  current.length = original.length ∧
    ∀ index < original.length, current[index]! =
      if index < offset then op.word original[index]! src[index]! else original[index]!

private theorem prefix_step (op : Operation) (original src current : Slice U64) (offset : Nat)
    (same : original.length = src.length) (active : offset < src.length)
    (inv : Prefix op original src current offset) :
    Prefix op original src (writeBlock op current src offset) (stopAt src offset) := by
  have equal : current.length = src.length := inv.1.trans same
  have stopEq : stopAt current offset = stopAt src offset := by simp only [stopAt, equal]
  let stop := stopAt src offset
  let values := blockWords op.kernel (pairAt current src offset offset)
  have width : values.length = stop - offset := by
    rw [block_words_len, stopEq]
  refine ⟨(block_write_length ..).trans inv.1, ?_⟩
  intro i room
  change (current.setSlice! offset values.val)[i]! = _
  by_cases before : i < offset
  · rw [Slice.setSlice!_getElem!_prefix _ _ _ _ before, inv.2 i room,
      ite_eq_left before, ite_eq_left (by unfold stop stopAt; omega : i < stop)]
  · by_cases after : stop ≤ i
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change offset + values.length ≤ i; omega),
        inv.2 i room, ite_eq_right before, ite_eq_right (by omega : ¬i < stop)]
    · rw [Slice.setSlice!_getElem!_middle _ _ _ _ (by
        change offset ≤ i ∧ i - offset < values.length ∧ i < current.length
        rw [inv.1]
        omega), ← Slice.getElem!_Nat_eq, ite_eq_left (by omega : i < stop)]
      change values[i - offset]! = _
      rw [block_word op current src equal offset (i - offset) (by rw [stopEq]; omega),
        show offset + (i - offset) = i by omega, inv.2 i room, ite_eq_right before]

inductive AllocatedTrace (op : Operation) (dstBase srcBase : Address) (permit : Address → Bool)
    (src : Slice U64) : Nat → Slice U64 → AddressHeap → Slice U64 → AddressHeap → Prop
  | done {offset dst heap} : src.length ≤ offset →
      AllocatedTrace op dstBase srcBase permit src offset dst heap dst heap
  | step {offset dst heap next final finalHeap} : offset < src.length →
      AllocatedBlock op dstBase srcBase permit dst src offset (stopAt src offset) heap next →
      AllocatedTrace op dstBase srcBase permit src (stopAt src offset)
        (writeBlock op dst src offset) next final finalHeap →
      AllocatedTrace op dstBase srcBase permit src offset dst heap final finalHeap

/-- The source order of every masked load and store over both complete
live slices. Each update preserves the separated shared source view and
the whole destination allocation for the following block. -/
theorem allocated_slice_scan (op : Operation) (live : LiveAllocations) (la57 : Bool)
    (dstBase srcBase : Address) (permit : Address → Bool) (original src current : Slice U64)
    (offset : Nat) (heap : AddressHeap) (same : original.length = src.length)
    (inv : Prefix op original src current offset)
    (dstView : WriteView live la57 heap permit dstBase (8 * current.length) 8)
    (dstBytes : FiniteWordWindow heap dstBase current.length (fun i => current[i]!.bv))
    (srcView : ReadView live la57 heap srcBase (8 * src.length) 8)
    (srcBytes : FiniteWordWindow heap srcBase src.length (fun i => src[i]!.bv))
    (apart : Disjoint dstBase (8 * original.length) srcBase (8 * src.length)) :
    let final := evalFrom op original src 0
    ∃ updated, AllocatedTrace op dstBase srcBase permit src offset current heap final updated ∧
      FiniteWordWindow updated dstBase final.length (fun i => final[i]!.bv) ∧
      WriteView live la57 updated permit dstBase (8 * final.length) 8 ∧
      FramesOutside heap updated dstBase (8 * original.length) := by
  suffices ∀ remaining offset current heap, src.length - offset = remaining →
      Prefix op original src current offset →
      WriteView live la57 heap permit dstBase (8 * current.length) 8 →
      FiniteWordWindow heap dstBase current.length (fun i => current[i]!.bv) →
      ReadView live la57 heap srcBase (8 * src.length) 8 →
      FiniteWordWindow heap srcBase src.length (fun i => src[i]!.bv) →
      let final := evalFrom op original src 0
      ∃ updated, AllocatedTrace op dstBase srcBase permit src offset current heap final updated ∧
        FiniteWordWindow updated dstBase final.length (fun i => final[i]!.bv) ∧
        WriteView live la57 updated permit dstBase (8 * final.length) 8 ∧
        FramesOutside heap updated dstBase (8 * original.length)
    from this _ _ current heap rfl inv dstView dstBytes srcView srcBytes
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro offset current heap count inv dstView dstBytes srcView srcBytes final
    by_cases active : offset < src.length
    · let stop := stopAt src offset
      have length : current.length = src.length := inv.1.trans same
      have stopEq : stopAt current offset = stop := by simp only [stop, stopAt, length]
      have progress : offset < stop := by unfold stop stopAt; omega
      obtain ⟨next, block, nextBytes, nextView, frame⟩ :=
        allocated_slice_block op live la57 heap permit dstBase srcBase current src offset length
          (by rwa [length]) dstView dstBytes srcView srcBytes
      have frameFull : FramesOutside heap next dstBase (8 * original.length) := by rwa [← inv.1]
      have nextSrc := frame_read_view frameFull apart srcView
      have nextSrcBytes := frame_word_view frameFull apart srcView.no_wrap srcBytes
      have progressed := prefix_step op original src current offset same active inv
      have newBytes : FiniteWordWindow next dstBase (writeBlock op current src offset).length
          (fun i => (writeBlock op current src offset)[i]!.bv) := by simpa only [block_write_length] using nextBytes
      have newView : WriteView live la57 next permit dstBase (8 * (writeBlock op current src offset).length) 8 :=
        by simpa only [block_write_length] using nextView
      obtain ⟨updated, later, result, outView, laterFrame⟩ :=
        ih (src.length - stop) (by omega) stop _ next rfl progressed newView newBytes nextSrc nextSrcBytes
      rw [stopEq] at block
      exact ⟨updated, .step active block later, result, outView, frameFull.trans laterFrame⟩
    · have finished : current = final := by
        apply Slice.ext_getElem (by simpa only [final, eval_length] using inv.1)
        intro i currentRoom finalRoom
        have inside : i < original.length := by rwa [inv.1] at currentRoom
        rw [Slice.Inhabited_getElem_eq_getElem! _ _ currentRoom, Slice.Inhabited_getElem_eq_getElem! _ _ finalRoom,
          inv.2 i inside, ite_eq_left (by omega : i < offset)]
        change _ = (evalFrom op original src 0)[i]!
        rw [eval_word op original src 0 i inside, ite_eq_left (Nat.zero_le _)]
      subst current
      exact ⟨heap, .done (by omega), dstBytes, dstView, fun _ _ => rfl⟩

#print axioms allocated_slice_scan

end BulksketchBridge.AvxSliceKernel
