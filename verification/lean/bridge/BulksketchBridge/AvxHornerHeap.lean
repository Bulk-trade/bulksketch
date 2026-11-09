import BulksketchBridge.AvxHorner
import BulksketchBridge.AvxSquareScalarMemory

namespace BulksketchBridge.AvxHorner

open Aeneas.Std Aeneas.Std.AvxHornerChunkRuntime
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc
open PortableHornerChallenges

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

private theorem window_eq_region (words : Slice U64) (offset stop : Nat) :
    window words offset stop = ClosedLeaf.region words offset stop := rfl

def writeBlock (leading : U64) (rest points out : Slice U64) (offset stop : Nat) : Slice U64 :=
  out.setSlice! offset (blockValues leading rest points out offset stop).val

@[simp] theorem write_block_length (leading : U64) (rest points out : Slice U64) (offset stop : Nat) :
    (writeBlock leading rest points out offset stop).length = out.length := Slice.setSlice!_length ..

/-- The original masked helper invocations of one Horner block, including
the exact field-derived register payload and complete outside-block byte frame. -/
structure AllocatedBlock (pointBase outBase : Address) (permit : Address → Bool)
    (leading : U64) (rest points out : Slice U64) (offset stop : Nat)
    (heap updated : AddressHeap) : Prop where
  load :
    let source := window points offset stop
    let address := pointBase + BitVec.ofNat 64 (8 * offset)
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨address.toNat, source.len⟩) =
      some (.register (loadWords source), liftHeap heap)
  store :
    let destination := window out offset stop
    let address := outBase + BitVec.ofNat 64 (8 * offset)
    exec (liftPermission permit) storeProgram
        (storeInput (liftHeap heap) ⟨address.toNat, destination.len⟩ (blockRegister leading rest points offset stop)) =
      some (.unit, liftHeap updated)
  frame :
    ∀ address : Address,
      address.toNat < outBase.toNat + 8 * offset ∨ outBase.toNat + 8 * stop ≤ address.toNat →
      updated address = heap address

theorem allocated_block (live : LiveAllocations) (la57 : Bool) (pointBase outBase : Address)
    (permit : Address → Bool) (leading : U64) (rest points out : Slice U64) (offset stop : Nat)
    (heap : AddressHeap) (active : offset < stop) (width : stop - offset ≤ 8)
    (pointRoom : stop ≤ points.length) (outRoom : stop ≤ out.length)
    (pointView : ReadView live la57 heap pointBase (8 * points.length) 8)
    (pointBytes : FiniteWordWindow heap pointBase points.length (fun i => points[i]!.bv))
    (outView : WriteView live la57 heap permit outBase (8 * out.length) 8)
    (outBytes : FiniteWordWindow heap outBase out.length (fun i => out[i]!.bv)) :
    let written := writeBlock leading rest points out offset stop
    ∃ updated, AllocatedBlock pointBase outBase permit leading rest points out offset stop heap updated ∧
      FiniteWordWindow updated outBase out.length (fun i => written[i]!.bv) ∧
      WriteView live la57 updated permit outBase (8 * out.length) 8 ∧
      FramesOutside heap updated outBase (8 * out.length) := by
  have load := load_allocated_window live la57 heap pointBase points permit offset stop active pointRoom width
    pointView pointBytes
  obtain ⟨updated, store, bytes, frame⟩ :=
    store_allocated_window live la57 heap outBase out permit (blockRegister leading rest points offset stop)
      offset stop active outRoom width outView outBytes
  have fit : (window out offset stop).length ≤ 8 := by
    rw [window_eq_region, ClosedLeaf.region_length _ _ _ outRoom]
    exact width
  have after : FiniteWordWindow updated outBase out.length
      (fun i => (writeBlock leading rest points out offset stop)[i]!.bv) := by
    unfold writeBlock blockValues
    rw [dite_eq_left fit]
    simpa only [window_eq_region] using bytes
  refine ⟨updated, ⟨load, store, frame⟩, after, write_view_from_words outView _ after, ?_⟩
  intro address outside
  apply frame
  omega

def Prefix (leading : U64) (rest points original current : Slice U64) (offset : Nat) : Prop :=
  current.length = original.length ∧ ∀ index, index < original.length →
    current[index]! = if index < offset then rest.val.reverse.foldl (stepWord points[index]!) leading
      else original[index]!

private theorem prefix_step (leading : U64) (rest points original current : Slice U64) (offset stop : Nat)
    (active : offset < stop) (width : stop - offset ≤ 8)
    (pointRoom : stop ≤ points.length) (outRoom : stop ≤ original.length)
    (inv : Prefix leading rest points original current offset) :
    Prefix leading rest points original (writeBlock leading rest points current offset stop) stop := by
  have currentRoom : stop ≤ current.length := by rwa [inv.1]
  let values := blockValues leading rest points current offset stop
  have valueLen : values.length = stop - offset := block_values_length _ _ _ _ _ _ currentRoom width
  refine ⟨(write_block_length ..).trans inv.1, ?_⟩
  intro i room
  change (current.setSlice! offset values.val)[i]! = _
  by_cases before : i < offset
  · rw [Slice.setSlice!_getElem!_prefix _ _ _ _ before, inv.2 i room,
      ite_eq_left before, ite_eq_left (by omega : i < stop)]
  · by_cases after : stop ≤ i
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change offset + values.length ≤ i; omega),
        inv.2 i room, ite_eq_right before, ite_eq_right (by omega : ¬i < stop)]
    · rw [Slice.setSlice!_getElem!_middle _ _ _ _ (by
        change offset ≤ i ∧ i - offset < values.length ∧ i < current.length
        omega), ← Slice.getElem!_Nat_eq, ite_eq_left (by omega : i < stop)]
      change (blockValues leading rest points current offset stop)[i - offset]! = _
      rw [block_value_word _ _ _ _ _ _ _ pointRoom currentRoom width (by omega),
        show offset + (i - offset) = i by omega]

inductive AllocatedTrace (pointBase outBase : Address) (permit : Address → Bool)
    (leading : U64) (rest points : Slice U64) :
    Nat → Slice U64 → AddressHeap → Slice U64 → AddressHeap → Prop
  | done {offset current heap} : points.length ≤ offset →
      AllocatedTrace pointBase outBase permit leading rest points offset current heap current heap
  | step {offset current heap next final finalHeap} : offset < points.length →
      AllocatedBlock pointBase outBase permit leading rest points current offset (blockEnd points offset) heap next →
      AllocatedTrace pointBase outBase permit leading rest points (blockEnd points offset)
        (writeBlock leading rest points current offset (blockEnd points offset)) next final finalHeap →
      AllocatedTrace pointBase outBase permit leading rest points offset current heap final finalHeap

theorem allocated_scan (live : LiveAllocations) (la57 : Bool) (pointBase outBase : Address)
    (permit : Address → Bool) (leading : U64) (rest points original current : Slice U64)
    (offset : Nat) (heap : AddressHeap)
    (aligned : original.length = points.length) (cursor : offset ≤ points.length)
    (inv : Prefix leading rest points original current offset)
    (pointView : ReadView live la57 heap pointBase (8 * points.length) 8)
    (pointBytes : FiniteWordWindow heap pointBase points.length (fun i => points[i]!.bv))
    (outView : WriteView live la57 heap permit outBase (8 * current.length) 8)
    (outBytes : FiniteWordWindow heap outBase current.length (fun i => current[i]!.bv))
    (apart : Disjoint outBase (8 * original.length) pointBase (8 * points.length)) :
    let final := evalFrom leading rest points original 0
    ∃ updated, AllocatedTrace pointBase outBase permit leading rest points offset current heap final updated ∧
      FiniteWordWindow updated outBase final.length (fun i => final[i]!.bv) ∧
      WriteView live la57 updated permit outBase (8 * final.length) 8 ∧
      FramesOutside heap updated outBase (8 * original.length) := by
  suffices ∀ remaining offset (current : Slice U64) (heap : AddressHeap),
      points.length - offset = remaining → offset ≤ points.length →
      Prefix leading rest points original current offset →
      ReadView live la57 heap pointBase (8 * points.length) 8 →
      FiniteWordWindow heap pointBase points.length (fun i => points[i]!.bv) →
      WriteView live la57 heap permit outBase (8 * current.length) 8 →
      FiniteWordWindow heap outBase current.length (fun i => current[i]!.bv) →
      let final := evalFrom leading rest points original 0
      ∃ updated, AllocatedTrace pointBase outBase permit leading rest points offset current heap final updated ∧
        FiniteWordWindow updated outBase final.length (fun i => final[i]!.bv) ∧
        WriteView live la57 updated permit outBase (8 * final.length) 8 ∧
        FramesOutside heap updated outBase (8 * original.length)
    from this (points.length - offset) offset current heap rfl cursor inv pointView pointBytes outView outBytes
  intro remaining
  induction remaining using Nat.strong_induction_on with
  | h remaining ih =>
    intro offset current heap exactCount cursor inv pointView pointBytes outView outBytes
    by_cases active : offset < points.length
    · let stop := blockEnd points offset
      have progress : offset < stop := by unfold stop blockEnd; omega
      have width : stop - offset ≤ 8 := by unfold stop blockEnd; omega
      have stopRoom : stop ≤ points.length := Nat.min_le_right _ _
      obtain ⟨next, block, nextBytes, nextView, frame⟩ := allocated_block live la57 pointBase outBase permit
        leading rest points current offset stop heap progress width stopRoom (by rw [inv.1, aligned]; exact stopRoom)
        pointView pointBytes outView outBytes
      have frameFull : FramesOutside heap next outBase (8 * original.length) := by rwa [← inv.1]
      have nextPoints := frame_read_view frameFull apart pointView
      have nextPointBytes := frame_word_view frameFull apart pointView.no_wrap pointBytes
      have advanced := prefix_step leading rest points original current offset stop progress width
        stopRoom (by rwa [aligned]) inv
      have nextWidth : (writeBlock leading rest points current offset stop).length = current.length := write_block_length ..
      have fullBytes : FiniteWordWindow next outBase (writeBlock leading rest points current offset stop).length
          (fun i => (writeBlock leading rest points current offset stop)[i]!.bv) := by rwa [nextWidth]
      have fullView : WriteView live la57 next permit outBase
          (8 * (writeBlock leading rest points current offset stop).length) 8 := by rwa [nextWidth]
      obtain ⟨updated, trace, finalBytes, finalView, finalFrame⟩ :=
        ih (points.length - stop) (by omega) stop (writeBlock leading rest points current offset stop)
          next rfl stopRoom advanced nextPoints nextPointBytes fullView fullBytes
      exact ⟨updated, .step active block trace, finalBytes, finalView, frameFull.trans finalFrame⟩
    · have complete : current = evalFrom leading rest points original 0 := by
        apply Slice.ext_getElem (by simp [inv.1])
        intro i currentBound outputBound
        have bounded : i < original.length := by rwa [← inv.1]
        rw [Slice.Inhabited_getElem_eq_getElem! _ _ currentBound,
          Slice.Inhabited_getElem_eq_getElem! _ _ outputBound, inv.2 i bounded,
          ite_eq_left (by omega : i < offset), eval_from_word _ _ _ _ _ _ bounded,
          ite_eq_left (Nat.zero_le _)]
      dsimp only
      rw [← complete]
      exact ⟨heap, .done (by omega), outBytes, outView, fun _ _ => rfl⟩

end BulksketchBridge.AvxHorner
