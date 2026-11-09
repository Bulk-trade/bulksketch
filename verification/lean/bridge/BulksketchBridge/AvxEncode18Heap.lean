import BulksketchBridge.AvxEncode18

namespace BulksketchBridge.AvxEncode18

open Aeneas.Std Aeneas.Std.AvxSquareRuntime Aeneas.Std.AvxEncode18Runtime Aeneas.Std.Avx512Register
open AvxSquare X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

attribute [local irreducible] rowPayload

def writeBlock (words : Slice U64) (value : Word512) (start stop : Nat) : Slice U64 :=
  let region := ClosedLeaf.region words start stop
  if fits : region.length ≤ 8 then words.setSlice! start (storeWords region value fits).val else words

@[simp] theorem write_block_length (words : Slice U64) (value : Word512) (start stop : Nat) :
    (writeBlock words value start stop).length = words.length := by
  unfold writeBlock
  dsimp only
  split <;> simp only [Slice.setSlice!_length]

private theorem write_block_word (words : Slice U64) (value : Word512) (start stop i : Nat)
    (room : stop ≤ words.length) (width : stop - start ≤ 8) (active : i < words.length) :
    (writeBlock words value start stop)[i]!.bv =
      if inside : start ≤ i ∧ i < stop then flatten value ⟨i - start, by omega⟩ else words[i]!.bv := by
  let region := ClosedLeaf.region words start stop
  have length : region.length = stop - start := ClosedLeaf.region_length _ _ _ room
  have fits : region.length ≤ 8 := by omega
  let written := storeWords region value fits
  have writtenLen : written.length = stop - start := by
    have equal : written.length = region.length := by simp [written, storeWords, registerPayload, Slice.length]
    exact equal.trans length
  have regionFits : (ClosedLeaf.region words start stop).length ≤ 8 := fits
  simp only [writeBlock, dite_eq_left regionFits]
  change (words.setSlice! start written.val)[i]!.bv = _
  by_cases inside : start ≤ i ∧ i < stop
  · rw [dite_eq_left inside, Slice.setSlice!_getElem!_middle _ _ _ _ (by
        change start ≤ i ∧ i - start < written.length ∧ i < words.length
        omega), ← Slice.getElem!_Nat_eq]
    exact store_word region value fits (i - start) (by omega)
  · rw [dite_eq_right inside]
    by_cases before : i < start
    · rw [Slice.setSlice!_getElem!_prefix _ _ _ _ before]
    · rw [Slice.setSlice!_getElem!_suffix _ _ _ _ (by change start + written.length ≤ i; omega)]

def BlockStore (base : Address) (permit : Address → Bool) (words : Slice U64)
    (value : Word512) (start stop : Nat) (before after : AddressHeap) : Prop :=
  let region := ClosedLeaf.region words start stop
  let address := base + BitVec.ofNat 64 (8 * start)
  exec (liftPermission permit) storeProgram (storeInput (liftHeap before) ⟨address.toNat, region.len⟩ value) =
    some (.unit, liftHeap after)

theorem allocated_store (live : LiveAllocations) (la57 : Bool) (base : Address) (permit : Address → Bool)
    (words : Slice U64) (value : Word512) (start stop : Nat) (heap : AddressHeap)
    (active : start < stop) (room : stop ≤ words.length) (width : stop - start ≤ 8)
    (view : WriteView live la57 heap permit base (8 * words.length) 8)
    (bytes : FiniteWordWindow heap base words.length (fun i => words[i]!.bv)) :
    let written := writeBlock words value start stop
    ∃ updated, BlockStore base permit words value start stop heap updated ∧
      FiniteWordWindow updated base written.length (fun i => written[i]!.bv) ∧
      WriteView live la57 updated permit base (8 * written.length) 8 ∧
      (∀ address : Address,
        address.toNat < base.toNat + 8 * start ∨ base.toNat + 8 * stop ≤ address.toNat →
          updated address = heap address) := by
  obtain ⟨updated, normal, bytes', frame⟩ :=
    store_allocated_window live la57 heap base words permit value start stop active room width view bytes
  have written : FiniteWordWindow updated base (writeBlock words value start stop).length
      (fun i => (writeBlock words value start stop)[i]!.bv) := by
    have fits : (ClosedLeaf.region words start stop).length ≤ 8 := by
      rw [ClosedLeaf.region_length _ _ _ room]
      exact width
    rw [write_block_length]
    simp only [writeBlock, dite_eq_left fits]
    exact bytes'
  have resized : WriteView live la57 heap permit base (8 * (writeBlock words value start stop).length) 8 := by
    simpa only [write_block_length] using view
  exact ⟨updated, normal, written, write_view_from_words resized _ written, frame⟩

def writeLow (odd : Slice U64) (values : Triple) : Slice U64 :=
  writeBlock odd values.1 0 8

def writeHigh (odd : Slice U64) (values : Triple) : Slice U64 :=
  writeBlock (writeLow odd values) values.2.1 8 16

def writeTail (odd : Slice U64) (values : Triple) : Slice U64 :=
  writeBlock (writeHigh odd values) values.2.2 16 18

theorem write_tail_word (odd : Slice U64) (values : Triple) (room : 18 ≤ odd.length)
    (i : Nat) (active : i < odd.length) :
    (writeTail odd values)[i]!.bv =
      if inside : i < 18 then rowLane values ⟨i, inside⟩ else odd[i]!.bv := by
  have lowLen : (writeLow odd values).length = odd.length := by simp [writeLow]
  have highLen : (writeHigh odd values).length = odd.length := by simp [writeHigh, writeLow]
  have last := write_block_word (writeHigh odd values) values.2.2 16 18 i
    (by rwa [highLen]) (by decide) (by rwa [highLen])
  have middle := write_block_word (writeLow odd values) values.2.1 8 16 i
    (by rw [lowLen]; omega) (by decide) (by rwa [lowLen])
  have first := write_block_word odd values.1 0 8 i (by omega) (by decide) active
  unfold writeTail
  rw [last]
  by_cases inRow : i < 18
  · rw [dite_eq_left inRow]
    unfold rowLane
    by_cases inTail : 16 ≤ i
    · simp only [dite_eq_left (And.intro inTail inRow), dite_eq_right (by omega : ¬i < 8),
        dite_eq_right (by omega : ¬i < 16)]
    · rw [dite_eq_right (by omega : ¬(16 ≤ i ∧ i < 18))]
      unfold writeHigh
      rw [middle]
      by_cases inHigh : 8 ≤ i
      · simp only [dite_eq_left (by omega : 8 ≤ i ∧ i < 16), dite_eq_right (by omega : ¬i < 8),
          dite_eq_left (by omega : i < 16)]
      · rw [dite_eq_right (by omega : ¬(8 ≤ i ∧ i < 16))]
        unfold writeLow
        rw [first]
        simp only [dite_eq_left (by omega : 0 ≤ i ∧ i < 8), dite_eq_left (by omega : i < 8), Nat.sub_zero]
  · rw [dite_eq_right inRow, dite_eq_right (by omega : ¬(16 ≤ i ∧ i < 18))]
    unfold writeHigh
    rw [middle, dite_eq_right (by omega : ¬(8 ≤ i ∧ i < 16))]
    unfold writeLow
    rw [first, dite_eq_right (by omega : ¬(0 ≤ i ∧ i < 8))]

/-- The original 8/8/2 masked store sequence on an admitted single live
allocation. The first 18 words agree with the exact typed return and
every byte outside that prefix is preserved. -/
def ActualAllocatedEncode18 : Prop :=
  ∀ (baseModel : Bases) (storeModel : Store), BasesLaw baseModel → StoreLaw storeModel →
  ∀ (live : LiveAllocations) (la57 : Bool) (base : Address) (permit : Address → Bool)
      (odd ids : Slice U64) (heap : AddressHeap) (room : 18 ≤ odd.length),
    (ids.length = 1 ∨ ids.length = 2) →
    WriteView live la57 heap permit base (8 * odd.length) 8 →
    FiniteWordWindow heap base odd.length (fun i => odd[i]!.bv) →
    ∃ values low high final,
      bulksketch.backend.x86_vpclmul512.encode_18 baseModel storeModel odd ids =
        .ok (odd.setSlice! 0 (rowPayload odd values room)) ∧
      BlockStore base permit odd values.1 0 8 heap low ∧
      BlockStore base permit (writeLow odd values) values.2.1 8 16 low high ∧
      BlockStore base permit (writeHigh odd values) values.2.2 16 18 high final ∧
      FiniteWordWindow final base odd.length (fun i => (odd.setSlice! 0 (rowPayload odd values room))[i]!.bv) ∧
      WriteView live la57 final permit base (8 * odd.length) 8 ∧
      FramesOutside heap final base (8 * 18)

theorem allocated_encode_refines : ActualAllocatedEncode18 := by
  intro baseModel storeModel basis storeLaw live la57 base permit odd ids heap room admitted view bytes
  obtain ⟨values, ran, _⟩ := encode_words baseModel basis storeModel storeLaw odd ids room admitted
  have lowLen : (writeLow odd values).length = odd.length := by simp [writeLow]
  have highLen : (writeHigh odd values).length = odd.length := by simp [writeHigh, writeLow]
  obtain ⟨low, first, lowBytes, lowView, lowFrame⟩ :=
    allocated_store live la57 base permit odd values.1 0 8 heap (by decide) (by omega) (by decide) view bytes
  obtain ⟨high, second, highBytes, highView, highFrame⟩ :=
    allocated_store live la57 base permit (writeLow odd values) values.2.1 8 16 low (by decide) (by rw [lowLen]; omega)
      (by decide) lowView lowBytes
  obtain ⟨final, third, finalBytes, finalView, finalFrame⟩ :=
    allocated_store live la57 base permit (writeHigh odd values) values.2.2 16 18 high (by decide) (by rwa [highLen])
      (by decide) highView highBytes
  have resultBytes :
      FiniteWordWindow final base odd.length (fun i => (odd.setSlice! 0 (rowPayload odd values room))[i]!.bv) := by
    intro i active byte
    have bytes : FiniteWordWindow final base (writeTail odd values).length
        (fun j => (writeTail odd values)[j]!.bv) := by
      unfold writeTail
      exact finalBytes
    have written : i < (writeTail odd values).length := by
      simp only [writeTail, write_block_length, highLen]
      exact active
    have heapBytes := bytes i written byte
    have tailWord := write_tail_word odd values room i active
    have matching : (writeTail odd values)[i]!.bv = (odd.setSlice! 0 (rowPayload odd values room))[i]!.bv := by
      rw [tailWord]
      by_cases inside : i < 18
      · have width := row_payload_length odd values room
        have read := Slice.setSlice!_getElem!_middle odd (rowPayload odd values room) 0 i
          (by rw [width]; omega)
        rw [Nat.sub_zero] at read
        rw [dite_eq_left inside, read]
        exact (row_payload_word odd values room ⟨i, inside⟩).symm
      · have width := row_payload_length odd values room
        have frame := Slice.setSlice!_getElem!_suffix odd (rowPayload odd values room) 0 i
          (by rw [width]; omega)
        rw [dite_eq_right inside, frame]
    dsimp only at heapBytes ⊢
    rw [matching] at heapBytes
    exact heapBytes
  have resultView : WriteView live la57 final permit base (8 * odd.length) 8 := by
    simpa only [write_block_length, highLen] using finalView
  refine ⟨values, low, high, final, ran, first, second, third, resultBytes, resultView, ?_⟩
  intro address outside
  rw [finalFrame address (by omega), highFrame address (by omega), lowFrame address (by omega)]

end BulksketchBridge.AvxEncode18
