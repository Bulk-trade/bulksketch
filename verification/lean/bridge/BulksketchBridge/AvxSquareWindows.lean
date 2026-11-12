import BulksketchBridge.AvxSquareAlgebra

namespace BulksketchBridge.AvxSquare

open Aeneas.Std Aeneas.Std.Avx512Register
open X86MaskedMemory X86MaskedMemory.Allocation X86MaskedMemory.Llbc

set_option maxRecDepth 4096

/-- Equality of every byte outside a physical interval. -/
def FramesOutside (before after : AddressHeap) (base : Address) (length : Nat) : Prop :=
  ∀ address, address.toNat < base.toNat ∨ base.toNat + length ≤ address.toNat →
    after address = before address

theorem FramesOutside.trans {first middle last : AddressHeap} {base : Address} {length : Nat}
    (earlier : FramesOutside first middle base length) (later : FramesOutside middle last base length) :
    FramesOutside first last base length := by
  intro address outside
  exact (later address outside).trans (earlier address outside)

private theorem byte_address (base : Address) (start offset : Nat)
    (room : base.toNat + 8 * start + offset < 2 ^ 64) :
    (base + BitVec.ofNat 64 (8 * start)) + BitVec.ofNat 64 offset =
      base + BitVec.ofNat 64 (8 * start + offset) := by
  have first : (base + BitVec.ofNat 64 (8 * start)).toNat = base.toNat + 8 * start :=
    address_add_exact _ _ (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [address_add_exact _ _ (by rw [first]; omega), first, address_add_exact _ _ (by omega), Nat.add_assoc]

/-- A nonempty source block uses the same live allocation as the whole
borrowed slice. The theorem derives an aligned subview and preserves
all byte indices without arithmetic wrap. -/
theorem read_word_window {live la57 heap base length} (view : ReadView live la57 heap base (8 * length) 8)
    (start count : Nat) (nonempty : 0 < count) (bound : start + count ≤ length) :
    ReadView live la57 heap (base + BitVec.ofNat 64 (8 * start)) (8 * count) 8 := by
  have room := view.no_wrap
  let chunk := base + BitVec.ofNat 64 (8 * start)
  have address : chunk.toNat = base.toNat + 8 * start := address_add_exact _ _ (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro empty
    have old : base.toNat ≠ 0 := by
      intro e
      exact view.nonnull (BitVec.eq_of_toNat_eq e)
    change chunk = 0 at empty
    rw [empty] at address
    simp at address
    omega
  · rw [address]
    have aligned := view.aligned
    omega
  · intro active
    obtain ⟨first, size, liveAlloc, extent, firstBound, contained⟩ := view.allocated (by omega)
    exact ⟨first, size, liveAlloc, extent, by rw [address]; omega, by rw [address]; omega⟩
  · intro offset active
    change (heap (chunk + BitVec.ofNat 64 offset)).isSome = true
    rw [byte_address base start offset (by omega)]
    exact view.initialized _ (by omega)

theorem write_word_window {live la57 heap permit base length}
    (view : WriteView live la57 heap permit base (8 * length) 8)
    (start count : Nat) (nonempty : 0 < count) (bound : start + count ≤ length) :
    WriteView live la57 heap permit (base + BitVec.ofNat 64 (8 * start)) (8 * count) 8 := by
  refine ⟨read_word_window view.toReadView start count nonempty bound, ?_⟩
  intro offset active
  rw [byte_address base start offset (by have room := view.toReadView.no_wrap; omega)]
  exact view.exclusive _ (by omega)

private theorem word_window_restrict (heap : AddressHeap) (base : Address) (words : Slice U64)
    (bytes : FiniteWordWindow heap base words.length (fun i => words[i]!.bv))
    (start stop : Nat) (ordered : start ≤ stop) (bound : stop ≤ words.length)
    (room : base.toNat + 8 * words.length ≤ 2 ^ 64) :
    FiniteWordWindow heap (base + BitVec.ofNat 64 (8 * start)) (stop - start)
      (fun i => (ClosedLeaf.region words start stop)[i]!.bv) := by
  intro index active byte
  have slot : start + index < words.length := by omega
  have offset : byte.val < 8 := byte.isLt
  rw [byte_address base start (8 * index + byte.val) (by omega),
    show 8 * start + (8 * index + byte.val) = 8 * (start + index) + byte.val by omega,
    bytes (start + index) slot byte]
  have read : (ClosedLeaf.region words start stop)[index]! = words[start + index]! := by
    simp only [ClosedLeaf.region, Slice.getElem!_Nat_eq, Slice.from_val]
    exact List.getElem!_slice start stop index words.val ⟨bound, by omega⟩
  simp only [read]

/-- Whole-table allocation hypotheses suffice for every original
nonempty masked load of a row subwindow. -/
theorem load_allocated_window (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (words : Slice U64) (permit : Address → Bool) (start stop : Nat)
    (ordered : start < stop) (bound : stop ≤ words.length) (limited : stop - start ≤ 8)
    (view : ReadView live la57 heap base (8 * words.length) 8)
    (bytes : FiniteWordWindow heap base words.length (fun i => words[i]!.bv)) :
    let window := ClosedLeaf.region words start stop
    let chunk := base + BitVec.ofNat 64 (8 * start)
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨chunk.toNat, window.len⟩) =
      some (.register (loadWords window), liftHeap heap) := by
  let window := ClosedLeaf.region words start stop
  let chunk := base + BitVec.ofNat 64 (8 * start)
  have len : window.length = stop - start := ClosedLeaf.region_length _ _ _ bound
  have admittedView : ReadView live la57 heap chunk (8 * window.length) 8 := by
    rw [len]
    exact read_word_window view start (stop - start) (by omega) (by omega)
  have admittedBytes : FiniteWordWindow heap chunk window.length (fun i => window[i]!.bv) := by
    rw [len]
    exact word_window_restrict heap base words bytes start stop (by omega) bound view.no_wrap
  exact square_load_allocated live la57 heap chunk window permit (by omega) admittedView admittedBytes

/-- One original masked store updates the corresponding word subwindow
of the whole destination while preserving every byte outside the block. -/
theorem store_allocated_window (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (base : Address) (words : Slice U64) (permit : Address → Bool) (value : Word512) (start stop : Nat)
    (ordered : start < stop) (bound : stop ≤ words.length) (limited : stop - start ≤ 8)
    (view : WriteView live la57 heap permit base (8 * words.length) 8)
    (bytes : FiniteWordWindow heap base words.length (fun i => words[i]!.bv)) :
    let window := ClosedLeaf.region words start stop
    let chunk := base + BitVec.ofNat 64 (8 * start)
    let fits : window.length ≤ 8 := by rwa [ClosedLeaf.region_length _ _ _ bound]
    let output := words.setSlice! start (storeWords window value fits).val
    ∃ updated : AddressHeap,
      exec (liftPermission permit) storeProgram (storeInput (liftHeap heap) ⟨chunk.toNat, window.len⟩ value) =
        some (.unit, liftHeap updated) ∧
      FiniteWordWindow updated base words.length (fun i => output[i]!.bv) ∧
      ∀ address, address.toNat < base.toNat + 8 * start ∨ base.toNat + 8 * stop ≤ address.toNat →
        updated address = heap address := by
  let window := ClosedLeaf.region words start stop
  let chunk := base + BitVec.ofNat 64 (8 * start)
  have len : window.length = stop - start := ClosedLeaf.region_length _ _ _ bound
  have fits : window.length ≤ 8 := by omega
  let stored := storeWords window value fits
  have storedLen : stored.length = window.length := by
    simp [stored, storeWords, registerPayload, Slice.length]
  let output := words.setSlice! start stored.val
  have room := view.toReadView.no_wrap
  have chunkAddress : chunk.toNat = base.toNat + 8 * start := address_add_exact _ _ (by omega)
  have admittedView : WriteView live la57 heap permit chunk (8 * window.length) 8 := by
    rw [len]
    exact write_word_window view start (stop - start) (by omega) (by omega)
  obtain ⟨updated, normal, written, frame⟩ :=
    square_store_allocated live la57 heap chunk window permit value fits admittedView
  have frame' (address : Address)
      (outside : address.toNat < base.toNat + 8 * start ∨ base.toNat + 8 * stop ≤ address.toNat) :
      updated address = heap address := by
    apply frame
    rw [chunkAddress, len]
    omega
  refine ⟨updated, normal, ?_, frame'⟩
  intro index active byte
  have byteRoom : byte.val < 8 := byte.isLt
  by_cases changed : start ≤ index ∧ index < stop
  · have localSlot : index - start < window.length := by omega
    have storedWord : output[index]! = stored[index - start]! := by
      simp only [output, Slice.getElem!_Nat_eq, Slice.setSlice!_val]
      apply List.getElem!_setSlice!_middle
      change start ≤ index ∧ index - start < stored.length ∧ index < words.length
      omega
    have writtenByte := written (index - start) localSlot byte
    change updated (chunk + BitVec.ofNat 64 (8 * (index - start) + byte.val)) =
      some (wordByte stored[index - start]!.bv byte) at writtenByte
    rw [show chunk = base + BitVec.ofNat 64 (8 * start) by rfl,
      byte_address base start _ (by omega),
      show 8 * start + (8 * (index - start) + byte.val) = 8 * index + byte.val by omega] at writtenByte
    dsimp only
    rw [storedWord]
    exact writtenByte
  · let address := base + BitVec.ofNat 64 (8 * index + byte.val)
    have exactAddress : address.toNat = base.toNat + 8 * index + byte.val := by
      rw [show address = base + BitVec.ofNat 64 (8 * index + byte.val) by rfl, address_add_exact _ _ (by omega),
        Nat.add_assoc]
    have unchanged := frame' address (by rw [exactAddress]; omega)
    have storedWord : output[index]! = words[index]! := by
      simp only [output, Slice.getElem!_Nat_eq, Slice.setSlice!_val]
      apply List.getElem!_setSlice!_same
      change index < start ∨ start + stored.length ≤ index
      omega
    change updated address = some (wordByte output[index]!.bv byte)
    rw [unchanged, storedWord]
    exact bytes index active byte

/-- A returned complete word view re-establishes initialized bytes for
the next block on the same exclusive allocation. -/
theorem write_view_from_words {live la57 heap updated permit base length}
    (view : WriteView live la57 heap permit base (8 * length) 8) (values : Nat → BitVec 64)
    (bytes : FiniteWordWindow updated base length values) :
    WriteView live la57 updated permit base (8 * length) 8 := by
  refine ⟨⟨view.nonnull, view.aligned, view.allocated, ?_⟩, view.exclusive⟩
  intro offset active
  let byte : Fin 8 := ⟨offset % 8, Nat.mod_lt _ (by decide)⟩
  have located := bytes (offset / 8) (by omega) byte
  have address : 8 * (offset / 8) + byte.val = offset := by dsimp [byte]; omega
  rw [address] at located
  rw [located]
  rfl

/-- After the scalar seed, one complete original AVX block has all of
its table loads, destination load and store justified by whole-slice
allocation views. The exact destination and preserved table views may
be carried to the next block. -/
theorem allocated_block (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap)
    (tableBase dstBase : Address) (table dst : Slice U64) (scratch : Slice Raw)
    (permit : Address → Bool) (offset stop : Nat)
    (active : offset < stop) (stopBound : stop ≤ dst.length) (limited : stop - offset ≤ 8)
    (inputBound : scratch.length ≤ dst.length) (tableBound : dst.length / 2 * dst.length ≤ table.length)
    (tableView : ReadView live la57 heap tableBase (8 * table.length) 8)
    (dstView : WriteView live la57 heap permit dstBase (8 * dst.length) 8)
    (tableBytes : FiniteWordWindow heap tableBase table.length (fun i => table[i]!.bv))
    (dstBytes : FiniteWordWindow heap dstBase dst.length (fun i => dst[i]!.bv))
    (apart : Disjoint dstBase (8 * dst.length) tableBase (8 * table.length)) :
    let degree := dst.length
    let first := (degree + 1) / 2
    let zero : Word512 := fun _ _ => 0
    let sums := scanRows scratch table degree first first offset stop zero zero (scratch.length - first)
    let destination := ClosedLeaf.region dst offset stop
    let chunk := dstBase + BitVec.ofNat 64 (8 * offset)
    let value := xorRegister (loadWords destination) (reduceRegisters sums.1 sums.2)
    let updatedWords := blockStep scratch table degree first offset stop dst
    (∀ i, first ≤ i → i < scratch.length →
      let start := (i - first) * degree
      let window := ClosedLeaf.region table (start + offset) (start + stop)
      let source := tableBase + BitVec.ofNat 64 (8 * (start + offset))
      exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨source.toNat, window.len⟩) =
        some (.register (loadWords window), liftHeap heap)) ∧
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨chunk.toNat, destination.len⟩) =
      some (.register (loadWords destination), liftHeap heap) ∧
    ∃ updated : AddressHeap,
      exec (liftPermission permit) storeProgram (storeInput (liftHeap heap) ⟨chunk.toNat, destination.len⟩ value) =
        some (.unit, liftHeap updated) ∧
      FiniteWordWindow updated dstBase dst.length (fun i => updatedWords[i]!.bv) ∧
      WriteView live la57 updated permit dstBase (8 * dst.length) 8 ∧
      ReadView live la57 updated tableBase (8 * table.length) 8 ∧
      FiniteWordWindow updated tableBase table.length (fun i => table[i]!.bv) ∧
      FramesOutside heap updated dstBase (8 * dst.length) := by
  let degree := dst.length
  let first := (degree + 1) / 2
  let zero : Word512 := fun _ _ => 0
  let sums := scanRows scratch table degree first first offset stop zero zero (scratch.length - first)
  let destination := ClosedLeaf.region dst offset stop
  let value := xorRegister (loadWords destination) (reduceRegisters sums.1 sums.2)
  refine ⟨?_, load_allocated_window live la57 heap dstBase dst permit offset stop active stopBound limited
    dstView.toReadView dstBytes, ?_⟩
  · intro i lower upper
    let start := (i - first) * degree
    have row : i - first + 1 ≤ degree / 2 := by omega
    have tableRoom : start + stop ≤ table.length := by
      have rowBound := (Nat.mul_le_mul_right degree row).trans tableBound
      rw [Nat.add_mul, Nat.one_mul] at rowBound
      omega
    exact load_allocated_window live la57 heap tableBase table permit (start + offset) (start + stop)
      (by omega) tableRoom (by omega) tableView tableBytes
  · obtain ⟨updated, normal, written, frame⟩ :=
      store_allocated_window live la57 heap dstBase dst permit value offset stop active stopBound limited
        dstView dstBytes
    have destLen : destination.length = stop - offset := ClosedLeaf.region_length _ _ _ stopBound
    have fits : destination.length ≤ 8 := by omega
    have exactOutput : blockStep scratch table degree first offset stop dst =
        dst.setSlice! offset (storeWords destination value fits).val := by
      unfold blockStep
      dsimp only
      rw [dite_eq_left (show (ClosedLeaf.region dst offset stop).length ≤ 8 from fits)]
    rw [← exactOutput] at written
    have tableFrame (byte : Nat) (inside : byte < 8 * table.length) :
        updated (tableBase + BitVec.ofNat 64 byte) = heap (tableBase + BitVec.ofNat 64 byte) := by
      have room := tableView.no_wrap
      have address := address_add_exact tableBase byte (by omega)
      apply frame
      rw [address]
      by_cases before : tableBase.toNat + byte < dstBase.toNat + 8 * offset
      · exact Or.inl before
      · refine Or.inr (Nat.le_of_not_gt ?_)
        intro overlaps
        exact apart (tableBase.toNat + byte) (by omega) (by omega) (by omega) (by omega)
    have tableView' : ReadView live la57 updated tableBase (8 * table.length) 8 := by
      refine ⟨tableView.nonnull, tableView.aligned, tableView.allocated, ?_⟩
      intro byte inside
      rw [tableFrame byte inside]
      exact tableView.initialized byte inside
    have tableBytes' : FiniteWordWindow updated tableBase table.length (fun i => table[i]!.bv) := by
      intro i inside byte
      rw [tableFrame (8 * i + byte.val) (by omega)]
      exact tableBytes i inside byte
    refine ⟨updated, normal, written, write_view_from_words dstView _ written, tableView', tableBytes', ?_⟩
    intro address outside
    apply frame
    omega

/-- A source block is the ordered family of read-only table views, its
read-only destination view, and the final original masked store. -/
def BlockExec (scratch : Slice Raw) (table : Slice U64) (degree first : Nat)
    (tableBase dstBase : Address) (permit : Address → Bool) (offset stop : Nat)
    (dst : Slice U64) (heap updated : AddressHeap) : Prop :=
  let zero : Word512 := fun _ _ => 0
  let sums := scanRows scratch table degree first first offset stop zero zero (scratch.length - first)
  let window := ClosedLeaf.region dst offset stop
  let chunk := dstBase + BitVec.ofNat 64 (8 * offset)
  let value := xorRegister (loadWords window) (reduceRegisters sums.1 sums.2)
  (∀ i, first ≤ i → i < scratch.length →
    let start := (i - first) * degree
    let row := ClosedLeaf.region table (start + offset) (start + stop)
    let source := tableBase + BitVec.ofNat 64 (8 * (start + offset))
    exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨source.toNat, row.len⟩) =
      some (.register (loadWords row), liftHeap heap)) ∧
  exec (liftPermission permit) loadProgram (loadInput (liftHeap heap) ⟨chunk.toNat, window.len⟩) =
    some (.register (loadWords window), liftHeap heap) ∧
  exec (liftPermission permit) storeProgram (storeInput (liftHeap heap) ⟨chunk.toNat, window.len⟩ value) =
    some (.unit, liftHeap updated)

inductive BlockTrace (scratch : Slice Raw) (table : Slice U64) (degree first : Nat)
    (tableBase dstBase : Address) (permit : Address → Bool) :
    Nat → Slice U64 → AddressHeap → Slice U64 → AddressHeap → Prop
  | done {offset dst heap} :
    degree ≤ offset → BlockTrace scratch table degree first tableBase dstBase permit offset dst heap dst heap
  | step {offset dst heap updated final finalHeap} :
    offset < degree →
    BlockExec scratch table degree first tableBase dstBase permit offset (min (offset + 8) degree) dst heap updated →
    BlockTrace scratch table degree first tableBase dstBase permit (min (offset + 8) degree)
      (blockStep scratch table degree first offset (min (offset + 8) degree) dst) updated final finalHeap →
    BlockTrace scratch table degree first tableBase dstBase permit offset dst heap final finalHeap

/-- All original vector memory operations realize the exact pure
block scan in one finite heap. The scalar seed's slice outputs are
the initial word views of this phase. -/
def ActualAllocatedAvxBlockScan : Prop :=
  ∀ (live : LiveAllocations) (la57 : Bool)
    (tableBase dstBase : Address) (table : Slice U64) (scratch : Slice Raw)
    (permit : Address → Bool) (degree fuel offset : Nat) (heap : AddressHeap) (dst : Slice U64)
    (_dstLen : dst.length = degree) (_enough : degree - offset ≤ fuel)
    (_inputBound : scratch.length ≤ degree) (_tableBound : degree / 2 * degree ≤ table.length)
    (_tableView : ReadView live la57 heap tableBase (8 * table.length) 8)
    (_dstView : WriteView live la57 heap permit dstBase (8 * degree) 8)
    (_tableBytes : FiniteWordWindow heap tableBase table.length (fun i => table[i]!.bv))
    (_dstBytes : FiniteWordWindow heap dstBase degree (fun i => dst[i]!.bv))
    (_apart : Disjoint dstBase (8 * degree) tableBase (8 * table.length)),
    let first := (degree + 1) / 2
    let final := scanBlocks scratch table degree first offset dst fuel
    ∃ finalHeap : AddressHeap,
      BlockTrace scratch table degree first tableBase dstBase permit offset dst heap final finalHeap ∧
      FiniteWordWindow finalHeap dstBase degree (fun i => final[i]!.bv) ∧
      WriteView live la57 finalHeap permit dstBase (8 * degree) 8 ∧
      ReadView live la57 finalHeap tableBase (8 * table.length) 8 ∧
      FiniteWordWindow finalHeap tableBase table.length (fun i => table[i]!.bv) ∧
      FramesOutside heap finalHeap dstBase (8 * degree)

theorem allocated_block_scan : ActualAllocatedAvxBlockScan := by
  intro live la57 tableBase dstBase table scratch permit degree fuel offset heap dst
    dstLen enough inputBound tableBound tableView dstView tableBytes dstBytes apart
  induction fuel generalizing offset heap dst with
  | zero =>
    exact ⟨heap, .done (by omega), dstBytes, dstView, tableView, tableBytes, fun _ _ => rfl⟩
  | succ fuel ih =>
    by_cases active : offset < degree
    · let stop := min (offset + 8) degree
      let first := (degree + 1) / 2
      have block := allocated_block live la57 heap tableBase dstBase table dst scratch permit offset stop
        (by dsimp [stop]; omega) (by omega) (by dsimp [stop]; omega) (by omega)
        (by rw [dstLen]; exact tableBound) tableView (by rw [dstLen]; exact dstView)
        tableBytes (by rw [dstLen]; exact dstBytes) (by rw [dstLen]; exact apart)
      simp only [dstLen] at block
      obtain ⟨reads, destRead, updated, wrote, exactBytes, nextDstView, nextTableView, nextTableBytes, frame⟩ := block
      let dst' := blockStep scratch table degree first offset stop dst
      have width : dst'.length = degree := (blockStep_length ..).trans dstLen
      have enough' : degree - stop ≤ fuel := by dsimp [stop]; omega
      obtain ⟨finalHeap, continued, finalBytes, finalDstView, finalTableView, finalTableBytes, finalFrame⟩ :=
        ih stop updated dst' width enough' nextTableView nextDstView nextTableBytes exactBytes
      refine ⟨finalHeap, ?_, ?_, finalDstView, finalTableView, finalTableBytes, frame.trans finalFrame⟩
      · simp only [scanBlocks, active, ite_true]
        exact .step active ⟨reads, destRead, wrote⟩ continued
      · simpa only [scanBlocks, active, ite_true] using finalBytes
    · have done : degree ≤ offset := by omega
      refine ⟨heap, ?_, ?_, dstView, tableView, tableBytes, fun _ _ => rfl⟩
      · simpa only [scanBlocks, active, ite_false] using
          (BlockTrace.done done : BlockTrace scratch table degree ((degree + 1) / 2)
            tableBase dstBase permit offset dst heap dst heap)
      · simpa only [scanBlocks, active, ite_false] using dstBytes

end BulksketchBridge.AvxSquare