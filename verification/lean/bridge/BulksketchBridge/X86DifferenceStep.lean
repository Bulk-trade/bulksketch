import BulksketchBridge.X86DifferenceGenerated

namespace BulksketchBridge.X86MaskedMemory.Difference

open Aeneas.Std Aeneas.Std.Avx512Register

def width (inputs : Inputs) (offset : Nat) : Nat := min (inputs.dst.len.val - offset) 8

def deltaWord (inputs : Inputs) (heap : Memory) (index : Nat) : BitVec 64 :=
  readLane heap (inputs.localWords.base + 8 * index) 0 ^^^
    readLane heap (inputs.remoteBytes.base + 8 * index) 0

def deltaRegister (inputs : Inputs) (heap : Memory) (offset : Nat) : Word512 :=
  unflatten fun lane => if lane.val < width inputs offset then deltaWord inputs heap (offset + lane.val) else 0

def MappedBytes (heap : Memory) (base count : Nat) : Prop :=
  ∀ offset, offset < count → (heap (base + offset)).isSome = true

private theorem wordRange_normal (view : Llbc.SliceView) (start stop : Nat)
    (order : start ≤ stop) (bounded : stop ≤ view.len.val) :
    ∃ window, wordRange view (start, stop) = some window ∧
      window.base = view.base + 8 * start ∧ window.len.val = stop - start := by
  have allowed : start ≤ stop ∧ stop ≤ view.len.val := ⟨order, bounded⟩
  unfold wordRange
  rw [dite_eq_left allowed]
  refine ⟨_, rfl, rfl, ?_⟩
  exact Usize.ofNatCore_val_eq _

private theorem byteAdd_normal (view : Llbc.SliceView) (offset : Nat) (bounded : offset ≤ view.len.val) :
    ∃ pointer, byteAdd view offset = some pointer ∧
      pointer.base = view.base + offset ∧ pointer.len.val = view.len.val - offset := by
  unfold byteAdd
  rw [dite_eq_left bounded]
  refine ⟨_, rfl, rfl, ?_⟩
  exact Usize.ofNatCore_val_eq _

theorem readLane_translate (heap : Memory) (base : Nat) (lane : Fin 8) :
    readLane heap base lane = readLane heap (base + 8 * lane.val) 0 := by
  unfold readLane
  congr 2

set_option maxHeartbeats 1000000 in
private theorem read_remote_normal (heap : Memory) (view : Llbc.SliceView) (n : Nat)
    (admitted : n ≤ 8) (inside : 8 * n ≤ view.len.val) (mapped : MappedBytes heap view.base (8 * n)) :
    ∃ mask, sourceMask n = some mask ∧ loadRemote heap mask view =
      some (unflatten fun lane => if lane.val < n then readLane heap view.base lane else 0, heap) := by
  let count := Usize.ofNatCore n (by scalar_tac)
  have exactCount : count.val = n := Usize.ofNatCore_val_eq _
  obtain ⟨mask, maskNormal, _, maskBits⟩ := X86LaneMask.mask_refines count (by omega)
  have bit (lane : Fin 8) : enabled mask.bv lane = decide (lane.val < n) := by
    simpa only [enabled, exactCount] using maskBits lane.val lane.isLt
  have active (offset : Fin 64) (selected : enabled mask.bv (laneOf offset) = true) :
      offset.val < 8 * n := by
    rw [bit, decide_eq_true_eq] at selected
    simp only [laneOf] at selected
    omega
  have region : ∀ offset : Fin 64, enabled mask.bv (laneOf offset) = true →
      offset.val < view.len.val := fun offset selected => (active offset selected).trans_le inside
  refine ⟨mask.bv, ?_, ?_⟩
  · unfold sourceMask
    rw [dite_eq_left admitted]
    change (match (bulksketch.backend.x86_vpclmul512.mask count).match with
      | .ok value => some value.bv
      | _ => none) = _
    rw [maskNormal, Result.match.ok]
  · have regionCheck : remoteCheck mask.bv view.len.val = true := by
      simp only [remoteCheck, List.all_eq_true, List.mem_finRange, true_implies]
      intro offset
      by_cases selected : enabled mask.bv (laneOf offset) = true
      · simp only [selected, ite_true, decide_eq_true_eq]
        exact region offset selected
      · simp only [ite_eq_right selected]
    have readable : Readable heap view.base mask.bv := fun offset selected =>
      mapped offset.val (active offset selected)
    have loadNormal : X86MaskedMemory.load heap view.base mask.bv =
        some ((fun lane => if lane.val < n then readLane heap view.base lane else 0), heap) := by
      simp only [X86MaskedMemory.load, (readCheck_iff heap view.base mask.bv).mpr readable, ite_true]
      apply congrArg (fun value : Lanes => some (value, heap))
      funext lane
      by_cases selected : lane.val < n
      · have enabledLane : enabled mask.bv lane = true := by
          simpa only [selected, decide_true] using bit lane
        simp only [enabledLane, selected, ite_true]
      · have disabled : enabled mask.bv lane = false := by
          simpa only [selected, decide_false] using bit lane
        simp only [disabled, selected, Bool.false_eq_true, ite_false]
    simp only [loadRemote, regionCheck, ite_true, loadNormal, Bind.bind, Option.bind]

private theorem load_words_normal (permit : Nat → Bool) (heap : Memory) (view : Llbc.SliceView)
    (admitted : view.len.val ≤ 8) (mapped : MappedBytes heap view.base (8 * view.len.val)) :
    loadWords permit heap view =
      some (unflatten fun lane => if lane.val < view.len.val then readLane heap view.base lane else 0, heap) := by
  rw [loadWords, load_mapped_window view admitted heap permit mapped]
  rfl

theorem step_refines (inputs : Inputs) (permit : Nat → Bool) (offset : Nat) (state : State)
    (active : offset < inputs.dst.len.val)
    (localLength : inputs.localWords.len.val = inputs.dst.len.val)
    (remoteLength : inputs.remoteBytes.len.val = 8 * inputs.dst.len.val)
    (localMapped : MappedBytes state.heap (inputs.localWords.base + 8 * offset) (8 * width inputs offset))
    (remoteMapped : MappedBytes state.heap (inputs.remoteBytes.base + 8 * offset) (8 * width inputs offset))
    (destination : WritableWindow state.heap permit (inputs.dst.base + 8 * offset) (width inputs offset)) :
    ∃ updated,
      differenceStep inputs permit offset state =
        some ⟨updated, orValue state.any (deltaRegister inputs state.heap offset)⟩ ∧
      WordWindow updated (inputs.dst.base + 8 * offset) (width inputs offset)
        (fun lane => deltaWord inputs state.heap (offset + lane)) ∧
      ∀ address, address < inputs.dst.base + 8 * offset ∨
        inputs.dst.base + 8 * (offset + width inputs offset) ≤ address →
        updated address = state.heap address := by
  let n := width inputs offset
  have nBound : n ≤ 8 := Nat.min_le_right _ _
  have endBound : offset + n ≤ inputs.dst.len.val := by
    have := Nat.min_le_left (inputs.dst.len.val - offset) 8
    dsimp only [n, width]
    omega
  have dstMax : inputs.dst.len.val ≤ Usize.max := by scalar_tac
  have remoteMax : inputs.remoteBytes.len.val ≤ Usize.max := by scalar_tac
  have subtraction : checkedSub inputs.dst.len.val offset = some (inputs.dst.len.val - offset) :=
    ite_eq_left (Nat.le_of_lt active)
  have finish : checked (offset + n) = some (offset + n) :=
    ite_eq_left (endBound.trans dstMax)
  have remoteOffset : checked (8 * offset) = some (8 * offset) := ite_eq_left (by omega)
  obtain ⟨left, leftRange, leftBase, leftLen⟩ :=
    wordRange_normal inputs.localWords offset (offset + n) (by omega) (by omega)
  obtain ⟨right, pointerAdd, rightBase, rightLen⟩ :=
    byteAdd_normal inputs.remoteBytes (8 * offset) (by omega)
  obtain ⟨dst, dstRange, dstBase, dstLen⟩ :=
    wordRange_normal inputs.dst offset (offset + n) (by omega) endBound
  have leftWidth : left.len.val = n := by omega
  have dstWidth : dst.len.val = n := by omega
  have localNormal := load_words_normal permit state.heap left (by omega) (by
    simpa only [leftBase, leftWidth] using localMapped)
  obtain ⟨mask, maskNormal, remoteNormal⟩ :=
    read_remote_normal state.heap right n nBound (by omega) (by simpa only [rightBase] using remoteMapped)
  let delta := deltaRegister inputs state.heap offset
  have deltaNormal : xorValue
      (unflatten fun lane => if lane.val < left.len.val then readLane state.heap left.base lane else 0)
      (unflatten fun lane => if lane.val < n then readLane state.heap right.base lane else 0) = delta := by
    funext pair high
    simp only [xorValue, unflatten, leftWidth, leftBase, rightBase, delta, deltaRegister, n]
    split
    · unfold deltaWord
      rw [readLane_translate state.heap (inputs.localWords.base + 8 * offset) (flatIndex pair high),
        readLane_translate state.heap (inputs.remoteBytes.base + 8 * offset) (flatIndex pair high)]
      rw [show inputs.localWords.base + 8 * offset + 8 * (flatIndex pair high).val =
          inputs.localWords.base + 8 * (offset + (flatIndex pair high).val) by omega,
        show inputs.remoteBytes.base + 8 * offset + 8 * (flatIndex pair high).val =
          inputs.remoteBytes.base + 8 * (offset + (flatIndex pair high).val) by omega]
    · rfl
  obtain ⟨updated, write, bytes, frame⟩ :=
    store_window dst (by omega) state.heap permit delta (by simpa only [dstBase, dstWidth] using destination)
  have storeNormal : storeWords permit state.heap dst delta = some updated := by
    rw [storeWords, write]
    rfl
  refine ⟨updated, ?_, ?_, ?_⟩
  · have exactWidth : min (inputs.dst.len.val - offset) 8 = n := rfl
    simp only [differenceStep, subtraction, exactWidth, finish, leftRange, localNormal, maskNormal,
      remoteOffset, pointerAdd, remoteNormal, dstRange, Bind.bind, Option.bind,
      deltaNormal, storeNormal]
    rfl
  · intro lane inside byte
    have bounded : lane < 8 := by omega
    have word := bytes lane (by omega : lane < dst.len.val) byte
    simpa only [dstBase, dite_eq_left bounded, delta, deltaRegister, flatten_unflatten,
      show lane < width inputs offset from inside, ite_true] using word
  · intro address outside
    apply frame
    rw [dstBase, dstWidth]
    omega

end BulksketchBridge.X86MaskedMemory.Difference
