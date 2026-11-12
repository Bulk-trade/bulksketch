import Arithmetic.AvxSliceKernelGenerated
import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxUpdateSingleBlock

open Aeneas Aeneas.Std Result
open Aeneas.Std.AvxSquareRuntime Aeneas.Std.Avx512Register
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc
open bulksketch.backend.x86_vpclmul512

set_option maxRecDepth 4096
set_option maxHeartbeats 1700000

def blockStop (odd : Slice U64) (start : Nat) := min (start + 8) odd.length

def blockRegister (odd : Slice U64) (start : Nat) (value : Word512) : Word512 :=
  fun pair high => loadWords (ClosedLeaf.region odd start (blockStop odd start)) pair high ^^^ value pair high

def blockOutput (odd : Slice U64) (start : Nat) (value : Word512) : Slice U64 :=
  let region := ClosedLeaf.region odd start (blockStop odd start)
  if fits : region.length ≤ 8 then
    odd.setSlice! start (storeWords region (blockRegister odd start value) fits).val
  else odd

/-- The original single-ID update computes its checked end, loads and
XORs the exact short or full block, and applies the original slice callback. -/
def ActualUpdateSingleBlock : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (odd : Slice U64) (offset : Usize) (value : Word512),
      offset.val + 8 ≤ Usize.max → offset.val ≤ odd.length →
      update_single_block load store odd offset value = .ok (blockOutput odd offset.val value)

theorem update_single_block_refines : ActualUpdateSingleBlock := by
  intro load store loadLaw storeLaw odd offset value addFits startFits
  obtain ⟨sum, addNormal, addValue⟩ := RawMulTable.normal_of_spec _ _
    (Usize.add_spec (x := offset) (y := 8#usize) addFits)
  let stop := core.cmp.impls.OrdUsize.min sum odd.len
  have stopVal : stop.val = blockStop odd offset.val := by
    simp only [stop, core.cmp.impls.OrdUsize.min_val, Slice.len_val, addValue, blockStop]
    rfl
  have ordered : offset.val ≤ stop.val := by rw [stopVal, blockStop]; omega
  have bound : stop.val ≤ odd.length := by rw [stopVal, blockStop]; omega
  obtain ⟨⟨window, back⟩, indexNormal, words, width, writeback⟩ :=
    RawMulTable.normal_of_spec _ _
      (core.slice.index.SliceIndexRangeUsizeSlice.index_mut.step_spec
        ⟨offset, stop⟩ odd (by exact ordered) (by exact bound))
  have exactWindow : window = ClosedLeaf.region odd offset.val (blockStop odd offset.val) := by
    apply Slice.ext
    simpa only [ClosedLeaf.region, Slice.from_val, ← stopVal] using words
  change window.length = stop.val - offset.val at width
  have fits : window.length ≤ 8 := by
    rw [width, stopVal, blockStop]
    omega
  have read := loadLaw window fits
  have write := storeLaw window (blockRegister odd offset.val value) fits
  unfold update_single_block
  simp only [addNormal, bind_ok, lift, Slice.index_mut_SliceIndexRangeUsizeSliceInst]
  rw [indexNormal, bind_ok]
  dsimp! only
  rw [read, bind_ok, xorWords, bind_ok]
  have regEq : (fun pair high => loadWords window pair high ^^^ value pair high) =
      blockRegister odd offset.val value := by rw [exactWindow]; rfl
  rw [regEq, write, bind_ok, writeback]
  simp only [blockOutput, ← exactWindow, dite_eq_left fits]

/-- The exact original masked calls of this block, linked to a complete
allocation view. No mutable activity outside the checked block is admitted. -/
def ActualAllocatedUpdateSingleBlock : Prop :=
  ∀ (load : Load) (store : Store), LoadLaw load → StoreLaw store →
    ∀ (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
      (permit : Address → Bool) (base : Address) (odd : Slice U64) (offset : Usize) (value : Word512),
      offset.val + 8 ≤ Usize.max → offset.val < odd.length →
      WriteView live la57 heap permit base (8 * odd.length) 8 →
      FiniteWordWindow heap base odd.length (fun i => odd[i]!.bv) →
      let stop := blockStop odd offset.val
      let region := ClosedLeaf.region odd offset.val stop
      let chunk := base + BitVec.ofNat 64 (8 * offset.val)
      let written := blockOutput odd offset.val value
      ∃ updated : AddressHeap,
        update_single_block load store odd offset value = .ok written ∧
        exec (liftPermission permit) loadProgram
          (loadInput (liftHeap heap) ⟨chunk.toNat, region.len⟩) =
            some (.register (loadWords region), liftHeap heap) ∧
        exec (liftPermission permit) storeProgram
          (storeInput (liftHeap heap) ⟨chunk.toNat, region.len⟩ (blockRegister odd offset.val value)) =
            some (.unit, liftHeap updated) ∧
        written.length = odd.length ∧
        FiniteWordWindow updated base odd.length (fun i => written[i]!.bv) ∧
        WriteView live la57 updated permit base (8 * odd.length) 8 ∧
        ∀ address, address.toNat < base.toNat + 8 * offset.val ∨ base.toNat + 8 * stop ≤ address.toNat →
          updated address = heap address

theorem allocated_update_single_block : ActualAllocatedUpdateSingleBlock := by
  intro load store loadLaw storeLaw live la57 heap permit base odd offset value addFits active view bytes
    stop region chunk written
  have ordered : offset.val < stop := by change _ < blockStop odd _; unfold blockStop; omega
  have bound : stop ≤ odd.length := Nat.min_le_right _ _
  have width : stop - offset.val ≤ 8 := by change blockStop odd _ - _ ≤ 8; unfold blockStop; omega
  have regionLen : region.length = stop - offset.val := ClosedLeaf.region_length _ _ _ bound
  have fits : region.length ≤ 8 := regionLen.trans_le width
  have read := load_allocated_window live la57 heap base odd permit offset.val stop ordered bound width
    view.toReadView bytes
  obtain ⟨updated, write, frameWords, unchanged⟩ :=
    store_allocated_window live la57 heap base odd permit (blockRegister odd offset.val value)
      offset.val stop ordered bound width view bytes
  have wordEq : written = odd.setSlice! offset.val (storeWords region (blockRegister odd offset.val value) fits).val := by
    unfold written blockOutput
    rw [dite_eq_left fits]
  have exactBytes : FiniteWordWindow updated base odd.length (fun i => written[i]!.bv) := by
    rw [wordEq]
    exact frameWords
  refine ⟨updated, update_single_block_refines load store loadLaw storeLaw odd offset value addFits (by omega),
    read, write, ?_, exactBytes, write_view_from_words view _ exactBytes, unchanged⟩
  rw [wordEq, Slice.setSlice!_length]

#print axioms update_single_block_refines
#print axioms allocated_update_single_block

end BulksketchBridge.AvxUpdateSingleBlock
