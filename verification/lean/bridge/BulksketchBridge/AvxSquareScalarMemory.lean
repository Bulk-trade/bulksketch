import BulksketchBridge.AvxSquareWindows

namespace BulksketchBridge.AvxSquare

open Aeneas.Std X86MaskedMemory X86MaskedMemory.Allocation

set_option maxRecDepth 4096

/-- Scalar byte-store model for a single aligned u64 slot. The original
typed seed assignments are related to this model under explicit layout,
allocation and permission premises. -/
def scalarStore (heap : AddressHeap) (permit : Address → Bool)
    (base : Address) (slot : Nat) (word : BitVec 64) : Option AddressHeap :=
  let start := base.toNat + 8 * slot
  if (start % 8 == 0) && decide (start + 8 ≤ 2 ^ 64) &&
      (List.finRange 8).all (fun byte =>
        let address := base + BitVec.ofNat 64 (8 * slot + byte.val)
        (heap address).isSome && permit address) then
    some (fun address =>
      if inside : start ≤ address.toNat ∧ address.toNat < start + 8 then
        some (wordByte word ⟨address.toNat - start, by omega⟩)
      else heap address)
  else none

theorem scalar_store_slot {live la57 heap permit base count words}
    (view : WriteView live la57 heap permit base (8 * count) 8)
    (bytes : FiniteWordWindow heap base count words)
    (slot : Nat) (bound : slot < count) (word : BitVec 64) :
    ∃ updated : AddressHeap,
      scalarStore heap permit base slot word = some updated ∧
      FiniteWordWindow updated base count (fun index => if index = slot then word else words index) ∧
      WriteView live la57 updated permit base (8 * count) 8 ∧
      FramesOutside heap updated base (8 * count) := by
  have fits := view.toReadView.no_wrap
  have aligned : (base.toNat + 8 * slot) % 8 = 0 := by have := view.aligned; omega
  have storeRoom : base.toNat + 8 * slot + 8 ≤ 2 ^ 64 := by omega
  have permitted : (List.finRange 8).all (fun byte =>
      let address := base + BitVec.ofNat 64 (8 * slot + byte.val)
      (heap address).isSome && permit address) = true := by
    rw [List.all_eq_true]
    intro byte _
    simp only [Bool.and_eq_true]
    exact ⟨view.initialized _ (by have := byte.isLt; omega),
      view.exclusive _ (by have := byte.isLt; omega)⟩
  let start := base.toNat + 8 * slot
  let updated : AddressHeap := fun address =>
    if inside : start ≤ address.toNat ∧ address.toNat < start + 8 then
      some (wordByte word ⟨address.toNat - start, by omega⟩)
    else heap address
  have normal : scalarStore heap permit base slot word = some updated := by
    simp only [scalarStore, aligned, beq_self_eq_true, storeRoom, decide_true, permitted,
      Bool.and_self, ite_true, updated, start]
  have result : FiniteWordWindow updated base count (fun index => if index = slot then word else words index) := by
    intro index active byte
    have byteRoom := byte.isLt
    have address := address_add_exact base (8 * index + byte.val) (by omega)
    unfold updated
    dsimp only
    by_cases same : index = slot
    · subst index
      rw [ite_eq_left rfl, dite_eq_left (by rw [address]; dsimp [start]; omega)]
      congr 2
      apply Fin.ext
      change (base + BitVec.ofNat 64 (8 * slot + byte.val)).toNat - (base.toNat + 8 * slot) = byte.val
      rw [address]
      omega
    · rw [ite_eq_right same, dite_eq_right (by rw [address]; dsimp [start]; omega)]
      exact bytes index active byte
  refine ⟨updated, normal, result, write_view_from_words view _ result, ?_⟩
  intro address outside
  exact dite_eq_right (by dsimp [start]; omega)

theorem disjoint_outside {dst src : Address} {written read : Nat}
    (apart : Disjoint dst written src read)
    (fits : src.toNat + read ≤ 2 ^ 64) (offset : Nat) (inside : offset < read) :
    let address := src + BitVec.ofNat 64 offset
    address.toNat < dst.toNat ∨ dst.toNat + written ≤ address.toNat := by
  dsimp only
  rw [address_add_exact _ _ (by omega)]
  by_cases below : src.toNat + offset < dst.toNat
  · exact Or.inl below
  · refine Or.inr (Nat.le_of_not_gt ?_)
    intro overlaps
    exact apart (src.toNat + offset) (by omega) overlaps (by omega) (by omega)

theorem frame_preserves_byte {before after : AddressHeap} {dst src : Address} {written read : Nat}
    (frame : FramesOutside before after dst written) (apart : Disjoint dst written src read)
    (fits : src.toNat + read ≤ 2 ^ 64) (offset : Nat) (inside : offset < read) :
    after (src + BitVec.ofNat 64 offset) = before (src + BitVec.ofNat 64 offset) :=
  frame _ (disjoint_outside apart fits offset inside)

theorem frame_read_view {live la57 before after dst src written read alignment}
    (frame : FramesOutside before after dst written) (apart : Disjoint dst written src read)
    (view : ReadView live la57 before src read alignment) :
    ReadView live la57 after src read alignment := by
  refine ⟨view.nonnull, view.aligned, view.allocated, ?_⟩
  intro offset inside
  rw [frame_preserves_byte frame apart view.no_wrap offset inside]
  exact view.initialized offset inside

theorem frame_write_view {live la57 before after dst src written read alignment permit}
    (frame : FramesOutside before after dst written) (apart : Disjoint dst written src read)
    (view : WriteView live la57 before permit src read alignment) :
    WriteView live la57 after permit src read alignment :=
  ⟨frame_read_view frame apart view.toReadView, view.exclusive⟩

theorem frame_word_view {before after dst src written count words}
    (frame : FramesOutside before after dst written) (apart : Disjoint dst written src (8 * count))
    (fits : src.toNat + 8 * count ≤ 2 ^ 64) (bytes : FiniteWordWindow before src count words) :
    FiniteWordWindow after src count words := by
  intro index active byte
  rw [frame_preserves_byte frame apart fits _ (by have := byte.isLt; omega)]
  exact bytes index active byte

theorem Disjoint.flip {dst src written read} (apart : Disjoint dst written src read) :
    Disjoint src read dst written := by
  intro address srcBegin srcEnd dstBegin dstEnd
  exact apart address dstBegin dstEnd srcBegin srcEnd

/-- Consecutive scalar writes in the source fill phase. This describes
the source store effects, independent of the compiler's fill lowering. -/
inductive FillTrace (base : Address) (permit : Address → Bool) : Nat → Nat → AddressHeap → AddressHeap → Prop
  | done {start heap} : FillTrace base permit start 0 heap heap
  | step {start count heap next final} :
    scalarStore heap permit base start 0 = some next →
    FillTrace base permit (start + 1) count next final →
    FillTrace base permit start (count + 1) heap final

theorem fill_trace (live : LiveAllocations) (la57 : Bool)
    (heap : AddressHeap) (base : Address) (permit : Address → Bool) (words : Nat → BitVec 64)
    (width start count : Nat) (room : start + count ≤ width)
    (view : WriteView live la57 heap permit base (8 * width) 8)
    (bytes : FiniteWordWindow heap base width words) :
    ∃ final : AddressHeap,
      FillTrace base permit start count heap final ∧
      FiniteWordWindow final base width (fun i => if start ≤ i ∧ i < start + count then 0 else words i) ∧
      WriteView live la57 final permit base (8 * width) 8 ∧
      FramesOutside heap final base (8 * width) := by
  induction count generalizing heap start words with
  | zero =>
    refine ⟨heap, .done, ?_, view, fun _ _ => rfl⟩
    intro i active byte
    simpa only [ite_eq_right (by omega : ¬ (start ≤ i ∧ i < start + 0))] using bytes i active byte
  | succ count ih =>
    obtain ⟨next, wrote, nextBytes, nextView, frame⟩ :=
      scalar_store_slot view bytes start (by omega) 0
    obtain ⟨final, trace, finalBytes, finalView, finalFrame⟩ :=
      ih next (fun i => if i = start then 0 else words i) (start + 1) (by omega) nextView nextBytes
    refine ⟨final, .step wrote trace, ?_, finalView, frame.trans finalFrame⟩
    intro i active byte
    have value := finalBytes i active byte
    by_cases filled : start ≤ i ∧ i < start + (count + 1)
    · by_cases same : i = start
      · subst i
        simpa only [ite_eq_right (by omega : ¬ (start + 1 ≤ start ∧ start < start + 1 + count)),
          ite_eq_left (by omega : start ≤ start ∧ start < start + (count + 1)), ite_eq_left rfl, ite_true] using value
      · simpa only [ite_eq_left filled, ite_eq_left (by omega : start + 1 ≤ i ∧ i < start + 1 + count)] using value
    · simpa only [ite_eq_right filled, ite_eq_right (by omega : ¬ (start + 1 ≤ i ∧ i < start + 1 + count)),
        ite_eq_right (by omega : i ≠ start)] using value

open scoped BulksketchBridge.DenseMulReductionSpec

/-- Physical words in the chosen x86_64 RawProduct layout from the
pinned LLBC. This is a two-word stride, with lo at byte 0 and hi at
byte 8. Callers supply this layout's byte view as a premise. -/
def scratchWord (scratch : Slice Raw) (slot : Nat) : BitVec 64 :=
  let value := scratch[slot / 2]!
  if slot % 2 = 0 then value.lo.bv else value.hi.bv

private theorem scratch_word_update (scratch : Slice Raw) (index slot : Nat)
    (bounded : index < scratch.length) (word : U64) :
    scratchWord (scratch.setAtNat index {scratch[index]! with lo := word}) slot =
      if slot = 2 * index then word.bv else scratchWord scratch slot := by
  by_cases same : index = slot / 2
  · have read : (scratch.setAtNat index {scratch[index]! with lo := word})[slot / 2]! =
        {scratch[index]! with lo := word} := by
      simp only [Slice.getElem!_Nat_eq]
      simpa only [same, Slice.getElem!_Nat_eq] using Slice.getElem!_Nat_setAtNat_eq scratch index {scratch[index]! with lo := word} bounded
    unfold scratchWord
    dsimp only
    rw [read]
    by_cases low : slot % 2 = 0
    · have hit : slot = 2 * index := by omega
      rw [ite_eq_left low, ite_eq_left hit]
    · have miss : slot ≠ 2 * index := by omega
      rw [ite_eq_right low, ite_eq_right miss, ite_eq_right low, ← same]
  · have miss : slot ≠ 2 * index := by omega
    have read : (scratch.setAtNat index {scratch[index]! with lo := word})[slot / 2]! =
        scratch[slot / 2]! := by
      simp only [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ same]
    simp only [scratchWord, read, ite_eq_right miss]

private theorem word_view_set {heap base} (words : Slice U64) (index : Nat) (value : U64)
    (bytes : FiniteWordWindow heap base words.length (fun i => if i = index then value.bv else words[i]!.bv)) :
    FiniteWordWindow heap base words.length (fun i => (words.setAtNat index value)[i]!.bv) := by
  intro i active byte
  have read := bytes i active byte
  dsimp only at read ⊢
  by_cases same : i = index
  · subst i
    simpa only [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_eq _ _ _ active, ite_eq_left rfl, ite_true] using read
  · simpa only [Slice.getElem!_Nat_eq, Slice.getElem!_Nat_setAtNat_ne _ _ _ _ (Ne.symm same),
      ite_eq_right same] using read

structure SeedViews (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (permit : Address → Bool)
    (inputBase dstBase scratchBase : Address) (input dst : Slice U64) (scratch : Slice Raw) : Prop where
  inputView : ReadView live la57 heap inputBase (8 * input.length) 8
  inputBytes : FiniteWordWindow heap inputBase input.length (fun i => input[i]!.bv)
  dstView : WriteView live la57 heap permit dstBase (8 * dst.length) 8
  dstBytes : FiniteWordWindow heap dstBase dst.length (fun i => dst[i]!.bv)
  scratchView : WriteView live la57 heap permit scratchBase (8 * (2 * scratch.length)) 8
  scratchBytes : FiniteWordWindow heap scratchBase (2 * scratch.length) (scratchWord scratch)

structure SeedDisjoint (inputBase dstBase scratchBase : Address) (inputWidth dstWidth scratchWidth : Nat) : Prop where
  dstInput : Disjoint dstBase (8 * dstWidth) inputBase (8 * inputWidth)
  scratchInput : Disjoint scratchBase (8 * (2 * scratchWidth)) inputBase (8 * inputWidth)
  scratchDst : Disjoint scratchBase (8 * (2 * scratchWidth)) dstBase (8 * dstWidth)

/-- The exact seed source order reads one input, writes its square into
scratch.lo, and writes dst[2*i] only for the low half. -/
def SeedExec (inputBase dstBase scratchBase : Address) (permit : Address → Bool)
    (index firstHigh : Nat) (coefficient : U64) (heap final : AddressHeap) : Prop :=
  let word := (Square.expectedWord coefficient).bv
  (∀ byte : Fin 8,
    heap (inputBase + BitVec.ofNat 64 (8 * index + byte.val)) = some (wordByte coefficient.bv byte)) ∧
  ∃ afterLo : AddressHeap,
    scalarStore heap permit scratchBase (2 * index) word = some afterLo ∧
    (if index < firstHigh then scalarStore afterLo permit dstBase (2 * index) word = some final
     else final = afterLo)

/-- All bytes outside both write slices remain unchanged. -/
def SeedFrame (before after : AddressHeap) (dstBase scratchBase : Address) (dstWidth scratchWidth : Nat) : Prop :=
  ∀ address,
    (address.toNat < dstBase.toNat ∨ dstBase.toNat + 8 * dstWidth ≤ address.toNat) →
    (address.toNat < scratchBase.toNat ∨ scratchBase.toNat + 8 * (2 * scratchWidth) ≤ address.toNat) →
    after address = before address

theorem SeedFrame.trans {first middle last : AddressHeap} {dstBase scratchBase : Address}
    {dstWidth scratchWidth : Nat}
    (earlier : SeedFrame first middle dstBase scratchBase dstWidth scratchWidth)
    (later : SeedFrame middle last dstBase scratchBase dstWidth scratchWidth) :
    SeedFrame first last dstBase scratchBase dstWidth scratchWidth := by
  intro address outsideDst outsideScratch
  exact (later address outsideDst outsideScratch).trans (earlier address outsideDst outsideScratch)

theorem seed_exec (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (permit : Address → Bool)
    (inputBase dstBase scratchBase : Address) (input dst : Slice U64) (scratch : Slice Raw)
    (index firstHigh : Nat) (active : index < input.length) (room : input.length ≤ scratch.length)
    (first : firstHigh = (dst.length + 1) / 2)
    (views : SeedViews live la57 heap permit inputBase dstBase scratchBase input dst scratch)
    (apart : SeedDisjoint inputBase dstBase scratchBase input.length dst.length scratch.length) :
    let next := seedStep input[index]! index firstHigh dst scratch
    ∃ updated : AddressHeap,
      SeedExec inputBase dstBase scratchBase permit index firstHigh input[index]! heap updated ∧
      SeedViews live la57 updated permit inputBase dstBase scratchBase input next.1 next.2 ∧
      SeedFrame heap updated dstBase scratchBase dst.length scratch.length := by
  let word := Square.expectedWord input[index]!
  let rawNext := scratch.setAtNat index {scratch[index]! with lo := word}
  obtain ⟨afterLo, wroteLo, afterLoBytes, afterLoView, loFrame⟩ :=
    scalar_store_slot views.scratchView views.scratchBytes (2 * index) (by omega) word.bv
  have rawLen : rawNext.length = scratch.length := Slice.setAtNat_length ..
  have rawBytes : FiniteWordWindow afterLo scratchBase (2 * scratch.length) (scratchWord rawNext) := by
    intro i bounded byte
    rw [scratch_word_update scratch index i (by omega) word]
    exact afterLoBytes i bounded byte
  have outputView := frame_write_view loFrame apart.scratchDst views.dstView
  have outputBytes := frame_word_view loFrame apart.scratchDst views.dstView.toReadView.no_wrap views.dstBytes
  have inputView := frame_read_view loFrame apart.scratchInput views.inputView
  have inputBytes := frame_word_view loFrame apart.scratchInput views.inputView.no_wrap views.inputBytes
  by_cases low : index < firstHigh
  · have dstSlot : 2 * index < dst.length := by omega
    obtain ⟨updated, wroteOut, updatedOut, updatedOutView, outFrame⟩ :=
      scalar_store_slot outputView outputBytes (2 * index) dstSlot word.bv
    refine ⟨updated, ⟨views.inputBytes index active, afterLo, wroteLo, ?_⟩, ?_, ?_⟩
    · rw [ite_eq_left low]
      exact wroteOut
    · simp only [seedStep, low, ite_true]
      refine ⟨frame_read_view outFrame apart.dstInput inputView,
        frame_word_view outFrame apart.dstInput inputView.no_wrap inputBytes, ?_, ?_, ?_, ?_⟩
      · rw [Slice.setAtNat_length]
        exact updatedOutView
      · rw [Slice.setAtNat_length]
        exact word_view_set dst (2 * index) word updatedOut
      · change WriteView live la57 updated permit scratchBase (8 * (2 * rawNext.length)) 8
        rw [rawLen]
        exact frame_write_view outFrame (Disjoint.flip apart.scratchDst) afterLoView
      · change FiniteWordWindow updated scratchBase (2 * rawNext.length) (scratchWord rawNext)
        rw [rawLen]
        exact frame_word_view outFrame (Disjoint.flip apart.scratchDst) afterLoView.toReadView.no_wrap rawBytes
    · intro address outsideDst outsideScratch
      exact (outFrame address outsideDst).trans (loFrame address outsideScratch)
  · refine ⟨afterLo, ⟨views.inputBytes index active, afterLo, wroteLo, by simp only [low, ite_false]⟩, ?_,
      fun address _ outside => loFrame address outside⟩
    simp only [seedStep, low, ite_false]
    refine ⟨inputView, inputBytes, outputView, outputBytes, ?_, ?_⟩
    · change WriteView live la57 afterLo permit scratchBase (8 * (2 * rawNext.length)) 8
      rw [rawLen]
      exact afterLoView
    · change FiniteWordWindow afterLo scratchBase (2 * rawNext.length) (scratchWord rawNext)
      rw [rawLen]
      exact rawBytes

/-- Seed execution follows the original forward enumeration and returns
the two exact typed slice values alongside the physical heap. -/
inductive SeedTrace (inputBase dstBase scratchBase : Address) (permit : Address → Bool)
    (input : Slice U64) (firstHigh : Nat) :
    Nat → Nat → Slice U64 → Slice Raw → AddressHeap → Slice U64 → Slice Raw → AddressHeap → Prop
  | done {index dst scratch heap} :
    SeedTrace inputBase dstBase scratchBase permit input firstHigh index 0 dst scratch heap dst scratch heap
  | step {index count dst scratch heap next finalDst finalScratch finalHeap} :
    index < input.length →
    SeedExec inputBase dstBase scratchBase permit index firstHigh input[index]! heap next →
    SeedTrace inputBase dstBase scratchBase permit input firstHigh (index + 1) count
      (seedStep input[index]! index firstHigh dst scratch).1
      (seedStep input[index]! index firstHigh dst scratch).2 next finalDst finalScratch finalHeap →
    SeedTrace inputBase dstBase scratchBase permit input firstHigh index (count + 1)
      dst scratch heap finalDst finalScratch finalHeap

theorem seed_trace (live : LiveAllocations) (la57 : Bool) (heap : AddressHeap) (permit : Address → Bool)
    (inputBase dstBase scratchBase : Address) (input dst : Slice U64) (scratch : Slice Raw)
    (index firstHigh count : Nat) (bounded : index + count ≤ input.length)
    (room : input.length ≤ scratch.length) (first : firstHigh = (dst.length + 1) / 2)
    (views : SeedViews live la57 heap permit inputBase dstBase scratchBase input dst scratch)
    (apart : SeedDisjoint inputBase dstBase scratchBase input.length dst.length scratch.length) :
    let final := seed input index firstHigh dst scratch count
    ∃ finalHeap : AddressHeap,
      SeedTrace inputBase dstBase scratchBase permit input firstHigh index count dst scratch heap
        final.1 final.2 finalHeap ∧
      SeedViews live la57 finalHeap permit inputBase dstBase scratchBase input final.1 final.2 ∧
      SeedFrame heap finalHeap dstBase scratchBase dst.length scratch.length := by
  induction count generalizing index heap dst scratch with
  | zero => exact ⟨heap, .done, views, fun _ _ _ => rfl⟩
  | succ count ih =>
    have active : index < input.length := by omega
    obtain ⟨next, executed, nextViews, frame⟩ :=
      seed_exec live la57 heap permit inputBase dstBase scratchBase input dst scratch index firstHigh active room first views apart
    let step := seedStep input[index]! index firstHigh dst scratch
    have dw : step.1.length = dst.length := seed_step_dst_length ..
    have sw : step.2.length = scratch.length := seed_step_scratch_length ..
    obtain ⟨finalHeap, trace, finalViews, finalFrame⟩ :=
      ih next step.1 step.2 (index + 1) (by omega) (by rw [sw]; exact room)
        (by rw [dw]; exact first) nextViews (by rw [dw, sw]; exact apart)
    rw [dw, sw] at finalFrame
    exact ⟨finalHeap, .step active executed trace, finalViews, frame.trans finalFrame⟩

end BulksketchBridge.AvxSquare
